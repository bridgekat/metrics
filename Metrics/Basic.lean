import Lean

/-!
# Shared state of the extractor

The configuration, the per-declaration mutable state and the caches that the passes of
`Metrics.Visit`, `Metrics.Hash` and `Metrics.Analyze` share.
-/

open Lean Meta

namespace Metrics

abbrev H := UInt64

@[inline] def mx (a b : H) : H := mixHash a b

def kLemma : H := 0x9E3779B97F4A7C15
def kBundle : H := 0xC2B2AE3D27D4EB4F
def kBVar : H := 0x165667B19E3779F9
def kSort : H := 0x27D4EB2F165667C5
def kConst : H := 0x85EBCA77C2B2AE63
def kApp : H := 0xFF51AFD7ED558CCD
def kLam : H := 0xC4CEB9FE1A85EC53
def kPi : H := 0x2545F4914F6CDD1D
def kLet : H := 0x9FB21C651E98DF25
def kProj : H := 0xD6E8FEB86659FD93
def kInst : H := 0xA0761D6478BD642F
def kFree : H := 0xE7037ED1A0B428DB
def kVar : H := 0x8EBC6AF09C88C6E3
def kMark : H := 0x589965CC75374CC3
def kLit : H := 0x1D8E4E27C47D124F

/-- Tree sizes saturate here: a proof term is a DAG, and its unfolding can be astronomically large. -/
def capN : Nat := 1000000000000000

@[inline] def sadd (a b : Nat) : Nat := min (a + b) capN

/-- What the extractor needs to know about the environment. -/
structure Cfg where
  env : Environment
  /-- By constant: 0 not a theorem, 1 a theorem counted as glue, 2 a theorem counted as a lemma. -/
  lemmaKind : Std.HashMap Name UInt8
  /-- The id of every constant, its row in `consts.tsv`. -/
  cid : Std.HashMap Name Nat
  /-- Lemma trees at least this large are recorded as fingerprints. -/
  minFp : Nat := 3
  /-- The auxiliary theorems the elaborator abstracts out of a proof (`foo._proof_1_2`,
  `foo._simp_1_3`): they are read as part of the proof that refers to them. -/
  aux : Std.HashSet Name := {}
  /-- The lemma sequence of a proof is cut here. -/
  seqCap : Nat := 4000
  /-- Constants that take the context's instances only to state their own type (matchers): being
  passed to one is not a use. -/
  neutral : Std.HashSet Name := {}

/-- What `visit` computes for a subterm. -/
structure VI where
  /-- Size as a tree. -/
  tree : Nat := 1
  depth : Nat := 1
  /-- The lemma forest: the outermost lemma applications of the subterm, each as the hash and the
  size of its tree of nested lemma applications. -/
  forest : Array (H × Nat) := #[]
  /-- For a term built from the declaration's class-typed binders by instance functions alone:
  the class it is an instance of, and the binders it is built from. -/
  chain : Option (Name × Array Nat) := none
  deriving Inhabited

/-- A use of a class-typed binder: the class it had been projected to when a consumer that is not
an instance function took it, that consumer, and the site (a binder's type, the conclusion or the
body). -/
structure Use where
  cls : Name
  consumer : Name
  /-- Which argument of the consumer it was. -/
  arg : Nat
  site : Nat

/-- The mutable state of a pass. The caches at the end outlive a declaration. -/
structure R where
  memo : IO.Ref (Std.HashMap USize VI)
  dag : IO.Ref Nat
  consts : IO.Ref (Std.HashMap Name Nat)
  fps : IO.Ref (Std.HashMap H Nat)
  uses : IO.Ref (Std.HashMap Nat (Array Use))
  occ : IO.Ref (Std.HashMap Nat Nat)
  /-- Per binder: how often it occurs as a direct argument of a constant, and of which
  constants at which positions. -/
  dcount : IO.Ref (Std.HashMap Nat Nat)
  direct : IO.Ref (Std.HashMap Nat (Array (Name × Nat)))
  site : IO.Ref Nat
  hmemo : IO.Ref (Std.HashMap USize H)
  /-- Proofs whose head is an auxiliary theorem, by address: the theorem's body applied to the
  arguments. Holding them here also keeps their addresses from being reused. -/
  auxExp : IO.Ref (Std.HashMap USize Expr)
  seq : IO.Ref (Array Nat)
  deadHave : IO.Ref Nat
  /-- The dead `have`s, as the bound name and the head constant of the unused proof. -/
  deadNames : IO.Ref (Array (Name × Name))
  binfo : IO.Ref (Std.HashMap Name (Array BinderInfo))
  resClass : IO.Ref (Std.HashMap Name (Option Name))
  chosen : IO.Ref (Std.HashMap Name Bool)

def R.new : BaseIO R := do
  return {
    memo := ← IO.mkRef {}, dag := ← IO.mkRef 0, consts := ← IO.mkRef {}, fps := ← IO.mkRef {}
    uses := ← IO.mkRef {}, occ := ← IO.mkRef {}, site := ← IO.mkRef 0, hmemo := ← IO.mkRef {}
    dcount := ← IO.mkRef {}, direct := ← IO.mkRef {}
    auxExp := ← IO.mkRef {}, seq := ← IO.mkRef #[], deadHave := ← IO.mkRef 0, deadNames := ← IO.mkRef #[]
    binfo := ← IO.mkRef {}, resClass := ← IO.mkRef {}, chosen := ← IO.mkRef {} }

def R.reset (r : R) : BaseIO Unit := do
  r.memo.set {}; r.dag.set 0; r.consts.set {}; r.fps.set {}; r.uses.set {}; r.occ.set {}
  r.auxExp.set {}; r.seq.set #[]; r.deadHave.set 0; r.deadNames.set #[]; r.dcount.set {}; r.direct.set {}

/-- The binder kinds of a constant's arguments. -/
def binfoOf (env : Environment) (n : Name) : Array BinderInfo := Id.run do
  let some ci := env.find? n | return #[]
  let mut t := ci.type
  let mut out := #[]
  repeat
    match t with
    | .forallE _ _ b bi => out := out.push bi; t := b
    | _ => break
  return out

def R.getBinfo (r : R) (env : Environment) (n : Name) : BaseIO (Array BinderInfo) := do
  if let some m := (← r.binfo.get)[n]? then return m
  let m := binfoOf env n
  r.binfo.modify (·.insert n m)
  return m

/-- The class a constant produces an instance of, if its type ends in a class. -/
def R.getResClass (r : R) (env : Environment) (n : Name) : BaseIO (Option Name) := do
  if let some m := (← r.resClass.get)[n]? then return m
  let m := match env.find? n with
    | none => none
    | some ci =>
      match ci.type.getForallBody.getAppFn with
      | .const k _ => if isClass env k then some k else none
      | _ => none
  r.resClass.modify (·.insert n m)
  return m

/--
Whether a constant builds an instance of a class without being a registered instance or a
projection: a structure put on a type by choice (one of the norms of a matrix), which is part of
what a statement says, unlike an instance that resolution would find anyway.
-/
def R.isChosenInst (r : R) (env : Environment) (n : Name) : BaseIO Bool := do
  if let some b := (← r.chosen.get)[n]? then return b
  let b ← match env.find? n with
    | some (.defnInfo _) =>
      if isInstanceCore env n || env.isProjectionFn n then pure false
      else pure (← r.getResClass env n).isSome
    | _ => pure false
  r.chosen.modify (·.insert n b)
  return b

def collapse (xs : Array (H × Nat)) : Array (H × Nat) :=
  if xs.size ≤ 8 then xs
  else #[(xs.foldl (fun h x => mx h x.1) kBundle, xs.foldl (fun s x => sadd s x.2) 0)]

/-- At most this many distinct uses are kept per binder; `R.flush` keeps the first ones, and a
binder that reaches the cap is reported as such. -/
def useCap : Nat := 64

def R.flush (r : R) (ch : Option (Name × Array Nat)) (consumer : Name) (arg : Nat := 0) :
    BaseIO Unit := do
  let some (cls, is) := ch | return
  let site ← r.site.get
  for i in is do
    r.uses.modify fun m =>
      let cur := m.getD i #[]
      if cur.size ≥ useCap ||
          cur.any (fun u => u.cls == cls && u.consumer == consumer && u.arg == arg && u.site == site)
      then m
      else m.insert i (cur.push { cls, consumer, arg, site })

/-- The declaration's binders, as free variables: index, class if class-typed, and whether a
hypothesis (a proof). -/
abbrev FVMap := Std.HashMap FVarId (Nat × Option Name × Bool)

end Metrics
