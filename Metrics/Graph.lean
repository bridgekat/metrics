import Lean

open Lean

namespace Metrics

/-- Indices in this array are preorder positions. Parent links encode ordered tree edges.
    A reference carries the index of the binder that introduced it. -/
structure Node where
  kind : String
  parent : Option Nat
  name : Option Name := none
  binder : Option Nat := none
  deriving Inhabited, ToJson

structure Graph where
  nodes : Array Node := #[]
  globals : Std.HashMap Name Nat := {}
  closed : Bool := false
  limit : Nat := 2000000
  deriving Inhabited

abbrev Build := StateT Graph (Except String)

def standardAxiom (n : Name) : Bool :=
  [`propext, `Classical.choice, `Quot.sound].contains n

def emit (kind : String) (parent : Option Nat) (name : Option Name := none)
    (binder : Option Nat := none) : Build Nat := do
  let i := (← get).nodes.size
  if i ≥ (← get).limit then throw s!"graph exceeds {(← get).limit} nodes"
  modify fun g => { g with nodes := g.nodes.push ⟨kind, parent, name, binder⟩ }
  return i

def reference (parent : Option Nat) (n : Name) : Build Unit := do
  if n == `sorryAx then throw "proof depends on sorryAx"
  let b := (← get).globals[n]?
  if (← get).closed && b.isNone && !standardAxiom n then throw s!"unresolved declaration {n}"
  discard <| emit (if b.isSome then "var" else "const") parent n b

partial def expr (e : Expr) (p : Option Nat) (scope : Array Nat := #[]) : Build Unit := do
  match e with
  | .bvar i =>
    if i ≥ scope.size then throw s!"unbound de Bruijn index {i}"
    discard <| emit "var" p none (some scope[scope.size - 1 - i]!)
  | .const n _ => reference p n
  | .lam n t b _ | .forallE n t b _ | .letE n t _ b _ =>
    let i ← emit (if e.isLambda then "lambda" else if e.isForall then "forall" else "let") p n
    expr t i scope
    if let .letE _ _ v _ _ := e then expr v i scope
    expr b i (scope.push i)
  | .app f a =>
    let i ← emit "app" p
    expr f i scope
    expr a i scope
  | .proj n idx b =>
    -- The structure name is an implicit global reference on this occurrence.
    let provider := (← get).globals[n]?
    if (← get).closed && provider.isNone then throw s!"unresolved projection structure {n}"
    let i ← emit s!"proj.{idx}" p n provider
    expr b i scope
  | .mdata _ b => expr b (← emit "mdata" p) scope
  | .sort _ => discard <| emit "sort" p
  | .lit _ => discard <| emit "lit" p
  | .fvar _ | .mvar _ => throw "open expression in compiled declaration"

/-- One event per end of a live interval. Each binder contributes once even if used repeatedly. -/
def measurements (g : Graph) : Json := Id.run do
  let mut last : Std.HashMap Nat Nat := {}
  let mut edges := 0
  for h : i in [:g.nodes.size] do
    if let some b := g.nodes[i].binder then
      last := last.insert b i
      edges := edges + 1
  -- Each subtree is a contiguous interval. Prefix differences count annotation nodes
  -- excluding metadata, while the end of the value interval sets let activation.
  let mut finish := Array.range g.nodes.size
  let mut sizes : Array Nat := #[0]
  for k in [:g.nodes.size] do
    let i := g.nodes.size - 1 - k
    if let some p := g.nodes[i]!.parent then
      finish := finish.set! p (max finish[p]! finish[i]!)
    sizes := sizes.push (sizes.back! + (if g.nodes[k]!.kind == "mdata" then 0 else 1))
  let mut events : Std.HashMap Nat (Int × Int) := {}
  let mut unused := #[]
  let mut params := #[]
  for h : i in [:g.nodes.size] do
    let node := g.nodes[i]
    let t := i + 1
    let isLet := node.kind == "let" || node.kind == "declLet"
    unless isLet || node.kind == "lambda" || node.kind == "forall" do continue
    let v := finish[t]! + 1
    if node.kind == "declLet" then
      let mut sig := t
      let mut val := v
      while sig < v && val ≤ finish[v]! do
        if g.nodes[sig]!.kind == "mdata" then sig := sig + 1
        else if g.nodes[val]!.kind == "mdata" then val := val + 1
        else if g.nodes[sig]!.kind == "forall" && g.nodes[val]!.kind == "lambda" then
          if !last.contains sig && !last.contains val then
            params := params.push <| Json.mkObj [("declaration", toJson node.name),
              ("name", toJson g.nodes[val]!.name), ("lambda", toJson val), ("forall", toJson sig)]
          sig := finish[sig+1]! + 1
          val := finish[val+1]! + 1
        else break
    if let some stop := last[i]? then
      let start := if isLet then finish[v]! else i
      let w : Int := (sizes[v]! - sizes[t]! : Nat)
      events := events.alter start fun v =>
        let (n, m) := v.getD (0, 0)
        some (n+1, m+w)
      events := events.alter stop fun v =>
        let (n, m) := v.getD (0, 0)
        some (n-1, m-w)
    else if node.kind == "let" then
      unused := unused.push <| Json.mkObj [("node", toJson i), ("name", toJson node.name)]
  let mut live := 0
  let mut load := 0
  let mut peak := 0
  let mut weighted := 0
  for i in [:g.nodes.size] do
    let (n, w) := events.getD i (0, 0)
    live := live + n
    load := load + w
    peak := max peak live
    weighted := max weighted load
  return Json.mkObj [("nodes", toJson g.nodes.size), ("references", toJson edges),
    ("width", toJson peak), ("weightedWidth", toJson weighted), ("unusedLets", toJson unused),
    ("unusedParameters", toJson params)]

end Metrics
