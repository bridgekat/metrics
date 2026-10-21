import Metrics.Visit
import Metrics.Hash

/-!
# The record of a declaration

`analyze` opens a declaration's statement into binders and conclusion, hashes the statement in
several normal forms, and (for a full record) measures the type and the proof term. It judges
nothing: the metrics are computed from these records by the scripts in `analysis/`. The README
defines every field.
-/

open Lean Meta

namespace Metrics

def hex (h : H) : String := String.ofList (Nat.toDigits 16 h.toNat)

def jstr (s : String) : String := (Json.str s).compress

def jarr (xs : Array String) : String := "[" ++ ",".intercalate xs.toList ++ "]"

def binderChar : BinderInfo → String
  | .default => "d" | .implicit => "i" | .strictImplicit => "s" | .instImplicit => "I"

def kindChar : ConstantInfo → String
  | .thmInfo _ => "t" | .defnInfo _ => "d" | .opaqueInfo _ => "o" | .axiomInfo _ => "a"
  | .quotInfo _ => "q" | .inductInfo _ => "i" | .ctorInfo _ => "c" | .recInfo _ => "r"

/-- Strip up to `n` leading lambdas. -/
def peelLams (v : Expr) (n : Nat) : Expr × Nat := Id.run do
  let mut v := v
  let mut k := 0
  repeat
    match v with
    | .lam _ _ b _ => if k < n then v := b; k := k + 1 else break
    | .mdata _ b => v := b
    | _ => break
  return (v, k)

def sortH (xs : Array H) : Array H := xs.qsort (· < ·)

/-- The size of a term as a tree, counted up to `fuel` nodes. -/
partial def sizeUpTo (e : Expr) (fuel : Nat) : Nat :=
  (go e fuel).1
where
  go (e : Expr) (fuel : Nat) : Nat × Nat :=
    if fuel == 0 then (0, 0) else
    match e with
    | .app f a =>
      let (n1, fuel) := go f (fuel - 1)
      let (n2, fuel) := go a fuel
      (n1 + n2 + 1, fuel)
    | .lam _ t b _ | .forallE _ t b _ =>
      let (n1, fuel) := go t (fuel - 1)
      let (n2, fuel) := go b fuel
      (n1 + n2 + 1, fuel)
    | .letE _ t v b _ =>
      let (n1, fuel) := go t (fuel - 1)
      let (n2, fuel) := go v fuel
      let (n3, fuel) := go b fuel
      (n1 + n2 + n3 + 1, fuel)
    | .mdata _ b | .proj _ _ b => go b fuel
    | _ => (1, fuel - 1)

/--
The record of one declaration, as the fields of a JSON object. `full` adds the measurements of the
type's and the proof term's contents to the statement hashes.
-/
unsafe def analyze (c : Cfg) (r : R) (ci : ConstantInfo) (full : Bool) : MetaM (Array String) := do
  let env := c.env
  forallTelescope ci.type fun xs concl => do
    let n := xs.size
    let decls ← xs.mapM fun x => x.fvarId!.getDecl
    let mut props : Array Bool := #[]
    let mut clss : Array (Option Name) := #[]
    for d in decls do
      props := props.push (← try isProp d.type catch _ => pure false)
      clss := clss.push <| match d.type.getAppFn with
        | .const k _ => if isClass env k then some k else none
        | _ => none
    let isInst (i : Nat) : Bool := (clss.getD i none).isSome
    let mut out : Array String := #[]
    -- statement hashes
    let h0 ← hashFresh { env, r, eraseInst := false, fvh := {} } ci.type
    let mut ordMap : Std.HashMap FVarId H := {}
    let mut rank := 0
    for i in [0:n] do
      if isInst i then ordMap := ordMap.insert decls[i]!.fvarId kInst
      else
        ordMap := ordMap.insert decls[i]!.fvarId (mx kVar (hash rank))
        rank := rank + 1
    let hcOrd : HCtx := { env, r, eraseInst := true, fvh := ordMap }
    let mut h1 : H := kPi
    for i in [0:n] do
      unless isInst i do h1 := mx h1 (← hashSymFresh hcOrd decls[i]!.type)
    h1 := mx h1 (← hashSymFresh hcOrd concl)
    -- colours: a binder is the hash of its type, with earlier binders replaced by theirs
    let mut c0 : Std.HashMap FVarId H := {}
    let mut c0s : Array H := #[]
    for i in [0:n] do
      let h ← if isInst i then pure kInst
        else hashSymFresh { env, r, eraseInst := true, fvh := c0 } decls[i]!.type
      c0 := c0.insert decls[i]!.fvarId h
      c0s := c0s.push h
    let hc0 ← hashSymFresh { env, r, eraseInst := true, fvh := c0 } concl
    let mut hh0 : Array H := #[]
    let mut hv0 : Array H := #[]
    -- per hypothesis: its binder, the constant at the head of its conclusion, its size, and how
    -- many quantifiers and premises it has itself
    let mut hmeta : Array String := #[]
    for i in [0:n] do
      unless isInst i do
        if props[i]! then
          hh0 := hh0.push c0s[i]!
          let head := match decls[i]!.type.getForallBody.getAppFn with
            | .const k _ => (c.cid[k]?).getD 0
            | _ => 0
          let depth := decls[i]!.type.getForallBinderNames.length
          hmeta := hmeta.push s!"[{i},{head},{sizeUpTo decls[i]!.type 2000},{depth}]"
        else hv0 := hv0.push c0s[i]!
    -- refined colours: a variable is also where it occurs
    let sites : Array Expr := (decls.map (·.type)).push concl
    let siteVars : Array (Array FVarId) := sites.map fun s => (collectFVars {} s).fvarIds
    let mut c1 := c0
    for i in [0:n] do
      if isInst i || props[i]! then continue
      let id := decls[i]!.fvarId
      let marked := c0.insert id kMark
      let mut sig : Array H := #[]
      for j in [i+1:n+1] do
        if j < n && isInst j then continue
        if siteVars[j]!.contains id then
          sig := sig.push (← hashSymFresh { env, r, eraseInst := true, fvh := marked } sites[j]!)
      c1 := c1.insert id ((sortH sig).foldl mx c0s[i]!)
    let hcRef : HCtx := { env, r, eraseInst := true, fvh := c1 }
    let mut fin : Array H := #[]
    for i in [0:n] do
      if isInst i then continue
      if props[i]! then fin := fin.push (← hashSymFresh hcRef decls[i]!.type)
      else fin := fin.push (c1.getD decls[i]!.fvarId kFree)
    let h2 := mx ((sortH fin).foldl mx kPi) (← hashSymFresh hcRef concl)
    out := out.push s!"\"h0\":\"{hex h0}\",\"h1\":\"{hex h1}\",\"h2\":\"{hex h2}\",\"hc\":\"{hex hc0}\""
    out := out.push s!"\"hh\":{jarr (hh0.map fun h => jstr (hex h))}"
    out := out.push s!"\"hv\":{jarr (hv0.map fun h => jstr (hex h))}"
    out := out.push s!"\"hm\":{jarr hmeta}"
    out := out.push s!"\"nb\":{n},\"np\":{props.foldl (fun k p => if p then k + 1 else k) 0}"
    if let .const k _ := concl.getAppFn then
      if let some id := c.cid[k]? then out := out.push s!"\"ch\":{id}"
    unless full do return out
    -- the type's contents
    let mut fv : FVMap := {}
    for i in [0:n] do fv := fv.insert decls[i]!.fvarId (i, clss[i]!, props[i]!)
    r.reset
    let mut ts := 0
    for j in [0:n+1] do
      r.site.set j
      r.memo.set {}
      let vi ← visit c r fv sites[j]!
      r.flush vi.chain `_
      ts := sadd ts vi.tree
    let td ← r.dag.get
    let tconsts := (← r.consts.get).toArray.filterMap fun (k, _) => c.cid[k]?
    let occT ← r.occ.get
    let dcT ← r.dcount.get
    out := out.push s!"\"ts\":{ts},\"td\":{td},\"tc\":{jarr (tconsts.map toString)}"
    -- the value's contents
    let mut occB : Std.HashMap Nat Nat := {}
    let mut dcB : Std.HashMap Nat Nat := {}
    let mut m := 0
    if let some v := ci.value? (allowOpaque := true) then
      let (body, k) := peelLams v n
      m := k
      let body := body.instantiateRev (xs.extract 0 k)
      r.memo.set {}; r.dag.set 0; r.consts.set {}; r.fps.set {}; r.occ.set {}; r.dcount.set {}
      r.auxExp.set {}; r.seq.set #[]; r.deadHave.set 0
      r.site.set (n + 1)
      let vi ← visit c r fv body
      r.flush vi.chain `_
      emitSeq c r body
      occB ← r.occ.get
      dcB ← r.dcount.get
      let vd ← r.dag.get
      let vconsts := (← r.consts.get).toArray.filterMap fun (k, cnt) =>
        (c.cid[k]?).map fun id => s!"[{id},{cnt}]"
      let fps := (← r.fps.get).toArray.map fun (h, sz) => s!"[\"{hex h}\",{sz}]"
      let sk := vi.forest.foldl (fun acc x => mx acc x.1) kBundle
      let skn := vi.forest.foldl (fun s x => sadd s x.2) 0
      let vh ← hashFresh hcOrd body
      out := out.push s!"\"vs\":{vi.tree},\"vd\":{vd},\"dp\":{vi.depth},\"pl\":{k}"
      out := out.push s!"\"vh\":\"{hex vh}\",\"sk\":[\"{hex sk}\",{skn}]"
      out := out.push s!"\"vc\":{jarr vconsts}"
      out := out.push s!"\"fp\":{jarr fps}"
      out := out.push s!"\"ls\":{jarr ((← r.seq.get).map toString)},\"dh\":{← r.deadHave.get}"
      let dn ← r.deadNames.get
      unless dn.isEmpty do
        out := out.push s!"\"dn\":{jarr (dn.map fun (n, h) => jarr #[jstr n.eraseMacroScopes.toString, jstr h.toString])}"
      if let .const k _ := body.getAppFn then
        if let some id := c.cid[k]? then
          out := out.push s!"\"bh\":{id},\"ba\":{body.getAppNumArgs}"
    -- the binders: kind, proposition?, class, occurrences in the statement and in the body (and
    -- how many of each are as a direct argument of a constant), the uses of a class-typed
    -- binder, the constants a binder is passed to directly, and its name
    let uses ← r.uses.get
    let direct ← r.direct.get
    let mut bs : Array String := #[]
    for i in [0:n] do
      let us := (uses.getD i #[]).map fun u =>
        s!"[{(c.cid[u.cls]?).getD 0},{(c.cid[u.consumer]?).getD 0},{u.arg},{u.site}]"
      let ds := (direct.getD i #[]).map fun (h, k) => s!"[{(c.cid[h]?).getD 0},{k}]"
      let cls := match clss[i]! with
        | some k => toString ((c.cid[k]?).getD 0)
        | none => "null"
      let body := if i < m then s!"{occB.getD i 0},{dcB.getD i 0}" else "null,null"
      let name := jstr (toString decls[i]!.userName)
      bs := bs.push s!"[\"{binderChar decls[i]!.binderInfo}\",{if props[i]! then 1 else 0},{cls},\
        {occT.getD i 0},{dcT.getD i 0},{body},{jarr us},{jarr ds},{name}]"
    out := out.push s!"\"b\":{jarr bs}"
    return out

end Metrics
