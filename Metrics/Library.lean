import Metrics.Graph

open Lean

namespace Metrics

inductive Boundary where
  | decl | file | module
  deriving BEq, Repr

structure Entry where
  info : ConstantInfo
  schema : Option (String × Array Name)
  deriving Inhabited

/-- A schema takes each external constant on which its specification depends once.
    The specification of a mutual inductive is the entire family's constructor signatures.
    Its own type names are internal to that schema. -/
def schemaArgs (env : Environment) (ci : ConstantInfo) : Except String (Option (String × Array Name)) := do
  unless ci matches .inductInfo _ | .ctorInfo _ | .recInfo _ | .quotInfo _ do return none
  let mut args := ci.type.getUsedConstantsAsSet
  let kind ← match ci with
    | .inductInfo ind => do
      for family in ind.all do
        let some (.inductInfo member) := env.find? family | throw s!"missing inductive {family}"
        args := args ++ member.type.getUsedConstantsAsSet
        for ctor in member.ctors do
          let some c := env.find? ctor | throw s!"missing constructor {ctor}"
          args := args ++ c.type.getUsedConstantsAsSet
      for family in ind.all do args := args.erase family
      pure "inductiveSchema"
    | .ctorInfo ctor => do
      args := args.insert ctor.induct
      pure "constructorSchema"
    | .recInfo recval => do
      for family in recval.all do args := args.insert family
      for rule in recval.rules do
        args := args.insert rule.ctor
        for dep in rule.rhs.getUsedConstants do
          -- Recursive calls within this mutual eliminator are schema-internal.
          if let some (.recInfo other) := env.find? dep then
            if other.all == recval.all then continue
          args := args.insert dep
      pure "recursorSchema"
    | .quotInfo _ => pure "quotientSchema"
    | _ => return none
  return some (kind, args.toArray.qsort Name.quickLt)

structure Plan where
  visiting : NameSet := {}
  seen : NameSet := {}
  entries : Array Entry := #[]

/-- Olean storage order is not guaranteed to put providers first. Visit prerequisites
    before consumers, using the stored order to break ties between root declarations. -/
partial def schedule (env : Environment) (included : Name → Bool) (n : Name) :
    StateT Plan (Except String) Unit := do
  if n == `sorryAx then throw "proof depends on sorryAx"
  unless included n do return
  if (← get).seen.contains n then return
  if (← get).visiting.contains n then throw s!"cyclic declaration dependency at {n}"
  let some ci := env.find? n | throw s!"missing declaration {n}"
  if ci matches .axiomInfo _ then
    if standardAxiom n then return
    throw s!"unsupported axiom {n}"
  modify fun s => { s with visiting := s.visiting.insert n }
  let schema ← liftM (schemaArgs env ci)
  let mut deps := ci.type.getUsedConstants
  if let some (_, args) := schema then
    deps := deps ++ args
  else if let some v := ci.value? true then
    deps := deps ++ v.getUsedConstants
  else throw s!"no value for {n}"
  for d in deps do schedule env included d
  modify fun s => {
    visiting := s.visiting.erase n
    seen := s.seen.insert n
    entries := s.entries.push ⟨ci, schema⟩ }

/-- Lean generalizes section parameters into the kernel telescope. Give a schema its
    own value-side binders so its parameter uses resolve in the scope of its value. -/
def schemaValue (ci : ConstantInfo) (kind : String) (args : Array Name) (root : Nat) : Build Unit := do
  let count := match ci with
    | .inductInfo i => i.numParams
    | .ctorInfo c => c.numParams
    | .recInfo r => r.numParams
    | _ => 0
  let mut parent := root
  let mut scope := #[]
  let mut type := ci.type
  for _ in [:count] do
    let .forallE n domain body _ := type.consumeMData | throw s!"missing schema parameter for {ci.name}"
    let b ← emit "lambda" parent n
    expr domain b scope
    scope := scope.push b
    parent := b
    type := body
  let s ← emit kind parent ci.name
  for arg in args do reference s arg
  for b in scope do discard <| emit "var" s none b

def telescope (entries : Array Entry) : Build Unit := do
  let mut parent := none
  for ⟨ci, schema⟩ in entries do
    let i ← emit "declLet" parent ci.name
    expr ci.type i
    if let some (kind, args) := schema then
      schemaValue ci kind args i
    else if let some v := ci.value? true then expr v i
    else throw s!"missing value for {ci.name}"
    modify fun g => { g with globals := g.globals.insert ci.name i }
    parent := some i
  discard <| emit "unit" parent

/-- Concatenate the included declarations in Lean's import order. The scheduler has
    already deduplicated them and put same-file prerequisites before consumers. -/
def inImportOrder (env : Environment) (entries : Array Entry) : Except String (Array Entry) := do
  let mut files := Array.replicate env.header.moduleNames.size (#[] : Array Entry)
  for e in entries do
    let some mi := env.getModuleIdxFor? e.info.name | throw s!"unknown owner of {e.info.name}"
    files := files.modify mi (·.push e)
  return files.flatten

/-- Import-only entry points still expose every file of the same library in their import DAG. -/
private def libraryFiles (env : Environment) (mod : Name) : NameSet := Id.run do
  let mut reached : NameSet := ({} : NameSet).insert mod
  let mut files : NameSet := {}
  let mods := env.header.moduleNames
  for k in [:mods.size] do
    let i := mods.size - 1 - k
    if reached.contains mods[i]! then
      if mod.getRoot.isPrefixOf mods[i]! then files := files.insert mods[i]!
      for imp in env.header.moduleData[i]!.imports do reached := reached.insert imp.module
  return files

def buildGraph (env : Environment) (mod : Name) (target : Option Name) (boundary : Boundary)
    (limit : Nat) : Except String Graph := do
  let some mi := env.header.moduleNames.idxOf? mod | throw s!"module not loaded: {mod}"
  let wholeFiles := if boundary == Boundary.module && target.isNone then libraryFiles env mod else {}
  let roots ← match target with
    | some n => do
      unless env.getModuleIdxFor? n == some mi do throw s!"{n} is not declared in {mod}"
      pure #[n]
    | none => do
      if boundary != .module then pure env.header.moduleData[mi]!.constNames
      else
        -- A barrel module may contain only imports. Include its library's imported
        -- files even when the barrel has no declarations to seed the closure.
        let mut roots := #[]
        for i in [:env.header.moduleNames.size] do
          if wholeFiles.contains env.header.moduleNames[i]! then
            roots := roots ++ env.header.moduleData[i]!.constNames
        pure roots
  let included := fun n => match boundary with
    | .decl => target == some n
    | .file => env.getModuleIdxFor? n == some mi
    | .module => true
  let (_, plan) ← (roots.forM (schedule env included)).run {}
  let entries ← if boundary == .module then inImportOrder env plan.entries else pure plan.entries
  let builder :=
    if let some ax := target.filter standardAxiom then reference none ax
    else telescope entries
  let (_, g) ← builder.run { limit, closed := boundary == Boundary.module }
  return g

end Metrics
