import Metrics.Library
import MetricsTest.Barrel

open Lean Metrics

private def check (condition : Bool) (msg : String) : IO Unit :=
  unless condition do throw (IO.userError msg)

/-- Independent, deliberately quadratic oracle for small graphs. Enumerate the live
    binders at each cut from child lists and reference positions. -/
private def verify (g : Graph) : IO Unit := do
  let mut children := Array.replicate g.nodes.size (Array.empty : Array Nat)
  let mut last : Std.HashMap Nat Nat := {}
  for h : i in [:g.nodes.size] do
    let n := g.nodes[i]
    if let some p := n.parent then
      check (p < i) "parent order"
      children := children.modify p (·.push i)
    if let some b := n.binder then last := last.insert b i
  let mut subtree := Array.replicate g.nodes.size 1
  let mut weights := subtree
  for k in [:g.nodes.size] do
    let i := g.nodes.size - 1 - k
    if g.nodes[i]!.kind == "mdata" then weights := weights.modify i (· - 1)
    if let some p := g.nodes[i]!.parent then
      subtree := subtree.modify p (· + subtree[i]!)
      weights := weights.modify p (· + weights[i]!)
  let mut peak := 0
  let mut weighted := 0
  for h : i in [:g.nodes.size] do
    if let some b := g.nodes[i].binder then
      let body := children[b]!.back!
      check (body ≤ i && i < body + subtree[body]!) "reference outside binder body"
  for cut in [:g.nodes.size] do
    let mut count := 0
    let mut load := 0
    for (b, stop) in last.toList do
      let kids := children[b]!
      let body := kids.back!
      let start := if kids.size == 3 then body - 1 else b
      if start ≤ cut && cut < stop then
        count := count + 1
        load := load + weights[kids[0]!]!
    peak := max count peak
    weighted := max load weighted
  let j := measurements g
  check ((j.getObjValAs? Nat "width").toOption == some peak) "width mismatch"
  check ((j.getObjValAs? Nat "weightedWidth").toOption == some weighted) "weighted width mismatch"

private def findNode (g : Graph) (k : String) (n : Name) : IO Nat :=
  IO.ofExcept <| (g.nodes.findIdx? fun v => v.kind == k && v.name == some n).elim
    (.error s!"missing {k} {n}") Except.ok

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `MetricsTest.Barrel}] {}
  let graph := fun m n b => IO.ofExcept (buildGraph env m n b 20000)
  let decl ← graph `MetricsTest.Cases (some `Fixture.conjunction) .decl
  verify decl
  let j := measurements decl
  check (decl.nodes.size == 56 && (j.getObjValAs? Nat "width").toOption == some 6 &&
    (j.getObjValAs? Nat "weightedWidth").toOption == some 6) "conjunction contract regression"
  let unused ← graph `MetricsTest.Cases (some `Fixture.unused) .decl
  check (((measurements unused).getObjValAs? (Array Json) "unusedParameters").toOption.get!.size == 1)
    "unused parameter"
  let file ← graph `MetricsTest.Base none .file
  verify file
  let element ← findNode file "declLet" `Fixture.Element
  let schema ← findNode file "inductiveSchema" `Fixture.Box
  check (file.nodes.any fun n => n.parent == some schema && n.binder == some element)
    "missing constructor-field dependency in the inductive schema"
  let ctor ← findNode file "declLet" `Fixture.Box.pack
  let recursor ← findNode file "recursorSchema" `Fixture.Box.rec
  check (file.nodes.any fun n => n.parent == some recursor && n.binder == some ctor)
    "missing recursor rule dependency"
  let tagged ← findNode file "inductiveSchema" `Fixture.Tagged
  let localArgs := file.nodes.filter fun n => n.parent == some tagged &&
    n.binder.any (fun b => file.nodes[b]!.kind == "lambda")
  check (localArgs.size == 2 && localArgs[0]!.binder != localArgs[1]!.binder)
    "missing generalized schema parameters"
  let linked ← graph `MetricsTest.Cases (some `Fixture.pair) .module
  verify linked
  let seed ← findNode linked "declLet" `Fixture.seed
  let left ← findNode linked "declLet" `Fixture.left
  let right ← findNode linked "declLet" `Fixture.right
  let pair ← findNode linked "declLet" `Fixture.pair
  check ((linked.nodes.filter fun n => n.kind == "declLet" && n.name == some `Fixture.seed).size == 1)
    "duplicated declaration through diamond import"
  for branch in #[left, right] do
    check (seed < branch && branch < pair) "import dependency order"
    check (linked.nodes.any fun n => n.parent == some branch && n.binder == some seed)
      "diamond branch does not refer directly to the shared declaration"
    check (linked.nodes.extract pair linked.nodes.size |>.any fun n => n.binder == some branch)
      "pair does not refer directly to each imported declaration"
  let mut parent := none
  for h : i in [:linked.nodes.size] do
    if linked.nodes[i].kind == "declLet" then
      check (linked.nodes[i].parent == parent) "broken top-level let chain"
      parent := some i
  check ((linked.nodes.filter (·.kind == "unit")).size == 1 &&
    linked.nodes.back!.kind == "unit" && linked.nodes.back!.parent == parent) "module terminator"
  check (!linked.nodes.any fun n => n.kind == "const") "unresolved constant in closed fixture"
  let barrel ← graph `MetricsTest.Barrel none .module
  discard <| findNode barrel "declLet" `Fixture.conjunction
  let cases ← graph `MetricsTest.Cases none .module
  check (toJson cases.nodes == toJson barrel.nodes) "empty barrel changed the flattened graph"
  check ((buildGraph env `MetricsTest.Cases (some `Fixture.conjunction) .decl 55).toOption.isNone) "node limit"
  let ty := mkSort .zero
  let e := Expr.lam `p ty (.letE `p (.mdata {} ty) (.bvar 0)
    (.letE `unused ty (.bvar 0) (.bvar 1) false) false) .default
  let (_, localGraph) ← IO.ofExcept ((expr e none).run {})
  verify localGraph
  check (((measurements localGraph).getObjValAs? Nat "width").toOption == some 1)
    "let activated inside its definition"
  check (((measurements localGraph).getObjValAs? (Array Json) "unusedLets").toOption.get!.size == 1)
    "shadowed unused let"
  check (((expr (.bvar 0) none).run {}).toOption.isNone) "unbound de Bruijn index"
  check (((expr (mkConst `sorryAx) none).run {}).toOption.isNone) "sorryAx accepted"
  IO.println "term graph checks passed"
