import Metrics.Basic

/-!
# The measuring pass

`visit` walks a term once, as a DAG, and computes its sizes, its lemma forest, the constants it
refers to, and how it uses the declaration's binders. `emitSeq` then reads off the lemma sequence.

Three conventions decide what a "step" of a proof is:

* An auxiliary theorem the elaborator abstracted out of a proof (`foo._proof_1_2`) is read as its
  body applied to its arguments, so a proof is measured whole wherever the elaborator cut it.
* A theorem is a *lemma* unless it is glue: declared in a logic or tactic module, an instance, or
  producing an instance. Glue is transparent to the lemma forest.
* The lemma forest follows explicit arguments only. Implicit arguments repeat, as data, proofs
  that are steps elsewhere (a subtype witness occurs in the type of everything built on it).
-/

open Lean Meta

namespace Metrics

/-- The body of an auxiliary theorem. -/
def auxValue? (c : Cfg) (n : Name) : Option Expr :=
  if c.aux.contains n then (c.env.find? n).bind (·.value? (allowOpaque := true)) else none

/-- The constant at the head of a proof, under binders and applications, or anonymous. -/
partial def headConst : Expr → Name
  | .mdata _ b | .lam _ _ b _ | .letE _ _ _ b _ => headConst b
  | .app f _ => headConst f
  | .const n _ => n
  | _ => .anonymous

/-- Whether a term is visibly a proof: headed by a theorem or by one of the hypotheses. -/
partial def proofHead (c : Cfg) (fv : FVMap) : Expr → Bool
  | .mdata _ b | .lam _ _ b _ | .letE _ _ _ b _ => proofHead c fv b
  | .app f _ => proofHead c fv f
  | .const n _ => c.lemmaKind.getD n 0 != 0
  | .fvar id => match fv[id]? with
    | some (_, _, p) => p
    | none => false
  | _ => false

mutual

/-- Measure a subterm, memoized on its address. -/
unsafe def visit (c : Cfg) (r : R) (fv : FVMap) (e : Expr) : BaseIO VI := do
  match e with
  | .bvar _ | .sort _ | .lit _ | .mvar _ => return {}
  | .const n _ =>
    r.consts.modify fun m => m.insert n (m.getD n 0 + 1)
    if let some v := auxValue? c n then return ← visit c r fv v
    if c.lemmaKind.getD n 0 == 2 then return { forest := #[(mx kLemma (hash n), 1)] } else return {}
  | .fvar id =>
    match fv[id]? with
    | some (i, cls?, _) =>
      r.occ.modify fun m => m.insert i (m.getD i 0 + 1)
      return { chain := cls?.map fun k => (k, #[i]) }
    | none => return {}
  | .mdata _ b => visit c r fv b
  | _ =>
    let key := ptrAddrUnsafe e
    if let some v := (← r.memo.get)[key]? then return v
    let v ← visitCore c r fv e
    r.memo.modify (·.insert key v)
    r.dag.modify (· + 1)
    return v

unsafe def visitCore (c : Cfg) (r : R) (fv : FVMap) (e : Expr) : BaseIO VI := do
  match e with
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    -- an auxiliary theorem is read as its body applied to the arguments
    if let .const n _ := f then
      if let some v := auxValue? c n then
        r.consts.modify fun m => m.insert n (m.getD n 0 + 1)
        let e' := v.beta args
        r.auxExp.modify (·.insert (ptrAddrUnsafe e) e')
        return ← visit c r fv e'
    -- `have _ := v; b` where `b` ignores the proof `v`: `v` is not part of the proof. (A lambda
    -- that ignores a *value* is everywhere in types, as a constant family applied to an index.)
    if let .lam n _ b _ := f then
      if args.size ≥ 1 && !b.hasLooseBVar 0 && proofHead c fv args[0]! then
        r.deadHave.modify (· + 1)
        r.deadNames.modify (·.push (n, headConst args[0]!))
        let bi ← visit c r fv b
        let mut tree := sadd bi.tree args.size
        let mut depth := bi.depth
        let mut kids := bi.forest
        for i in [1:args.size] do
          let ai ← visit c r fv args[i]!
          tree := sadd tree ai.tree
          depth := max depth ai.depth
          kids := kids ++ ai.forest
          r.flush ai.chain `_
        return { tree, depth := depth + 1, forest := collapse kids }
    let fi ← visit c r fv f
    let head? := f.constName?
    let bis ← match head? with
      | some h => r.getBinfo c.env h
      | none => pure #[]
    let mut tree := sadd fi.tree args.size
    let mut depth := fi.depth
    let mut kids : Array (H × Nat) := if f.isConst then #[] else fi.forest
    let mut chained : Array ((Name × Array Nat) × Nat) := #[]
    for i in [0:args.size] do
      let ai ← visit c r fv args[i]!
      tree := sadd tree ai.tree
      depth := max depth ai.depth
      if (bis.getD i .default).isExplicit then kids := kids ++ ai.forest
      if let some ch := ai.chain then chained := chained.push (ch, i)
      -- a binder passed on as it is: recorded so that "unused" can be followed through calls
      if let .fvar id := args[i]!.consumeMData then
        if let some (b, _, _) := fv[id]? then
          -- only when the head is a constant: an argument of a local hypothesis or function is
          -- a use like any other
          if let some h := head? then
            r.dcount.modify fun m => m.insert b (m.getD b 0 + 1)
            r.direct.modify fun m =>
              let cur := m.getD b #[]
              if cur.size ≥ 16 || cur.contains (h, i) then m else m.insert b (cur.push (h, i))
    r.flush fi.chain `_fn
    -- an instance function passes the binders it was given on; anything else consumes them
    let mut chain := none
    unless chained.isEmpty || (head?.any c.neutral.contains) do
      let rc ← match head? with
        | some h => r.getResClass c.env h
        | none => pure none
      match rc with
      | some q =>
        let mut is : Array Nat := #[]
        for (ch, _) in chained do
          for i in ch.2 do
            unless is.contains i do is := is.push i
        chain := some (q, is)
      | none =>
        for (ch, i) in chained do r.flush (some ch) (head?.getD `_) i
    let forest ← match head? with
      | some h =>
        if c.lemmaKind.getD h 0 == 2 then
          let hsh := kids.foldl (fun acc x => mx acc x.1) (mx kLemma (hash h))
          let sz := kids.foldl (fun s x => sadd s x.2) 1
          if sz ≥ c.minFp then r.fps.modify (·.insert hsh sz)
          pure #[(hsh, sz)]
        else pure (collapse kids)
      | none => pure (collapse kids)
    return { tree, depth := depth + 1, forest, chain }
  | .lam _ t b _ =>
    let ti ← visit c r fv t
    let bi ← visit c r fv b
    r.flush ti.chain `_
    r.flush bi.chain `_
    return { tree := sadd 1 (sadd ti.tree bi.tree), depth := max ti.depth bi.depth + 1,
             forest := bi.forest }
  | .forallE _ t b _ =>
    let ti ← visit c r fv t
    let bi ← visit c r fv b
    r.flush ti.chain `_
    r.flush bi.chain `_
    return { tree := sadd 1 (sadd ti.tree bi.tree), depth := max ti.depth bi.depth + 1 }
  | .letE n t v b _ =>
    let ti ← visit c r fv t
    let bi ← visit c r fv b
    r.flush ti.chain `_
    r.flush bi.chain `_
    if !b.hasLooseBVar 0 && proofHead c fv v then
      r.deadHave.modify (· + 1)
      r.deadNames.modify (·.push (n, headConst v))
      return { tree := sadd 1 (sadd ti.tree bi.tree), depth := max ti.depth bi.depth + 1,
               forest := bi.forest }
    let vi ← visit c r fv v
    r.flush vi.chain `_
    return { tree := sadd 1 (sadd ti.tree (sadd vi.tree bi.tree)),
             depth := max ti.depth (max vi.depth bi.depth) + 1,
             forest := collapse (vi.forest ++ bi.forest) }
  | .proj _ _ b =>
    let bi ← visit c r fv b
    r.flush bi.chain `_proj
    return { tree := sadd 1 bi.tree, depth := bi.depth + 1, forest := bi.forest }
  | _ => return {}

end

/--
The lemma sequence of a measured term: its lemma applications in the order of the term, along
explicit arguments, up to `seqCap`. A subterm without lemmas is not entered, which is what keeps
this tree walk from unfolding the DAG.
-/
unsafe def emitSeq (c : Cfg) (r : R) (e : Expr) : BaseIO Unit := do
  if (← r.seq.get).size ≥ c.seqCap then return
  match e with
  | .const n _ =>
    if let some v := auxValue? c n then emitSeq c r v
    else if c.lemmaKind.getD n 0 == 2 then
      if let some id := c.cid[n]? then r.seq.modify (·.push id)
  | .mdata _ b => emitSeq c r b
  | .app .. | .lam .. | .letE .. | .proj .. =>
    let key := ptrAddrUnsafe e
    let some vi := (← r.memo.get)[key]? | return
    if vi.forest.isEmpty then return
    match e with
    | .app .. =>
      if let some e' := (← r.auxExp.get)[key]? then return ← emitSeq c r e'
      let f := e.getAppFn
      let args := e.getAppArgs
      emitSeq c r f
      let bis ← match f.constName? with
        | some h => r.getBinfo c.env h
        | none => pure #[]
      for i in [0:args.size] do
        if (bis.getD i .default).isExplicit then emitSeq c r args[i]!
    | .lam _ _ b _ => emitSeq c r b
    | .letE _ _ v b _ => emitSeq c r v; emitSeq c r b
    | .proj _ _ b => emitSeq c r b
    | _ => return
  | _ => return

end Metrics
