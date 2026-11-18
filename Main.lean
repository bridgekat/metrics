import Metrics

open Lean Metrics

private def usage := "metrics (decl MODULE NAME | file MODULE | module MODULE [NAME]) [--graph] [--max-nodes N]\nmetrics dump --roots A,B --full A,B --out DIR [--shard i/n] [--max-nodes N]"

structure Options' where
  graph : Bool := false
  limit : Nat := 2000000
  roots : Array Name := #[]
  full : Array Name := #[]
  out : System.FilePath := "metrics-out"
  shard : Nat := 0
  shards : Nat := 1

def names (v : String) : Except String (Array Name) := do
  let parts := v.splitOn ","
  if parts.any String.isEmpty then throw "expected comma-separated module names"
  return parts.toArray.map String.toName

def options (dump : Bool) (o : Options') : List String → Except String Options'
  | [] => return o
  | "--graph" :: rest => options dump {o with graph := true} rest
  | "--max-nodes" :: v :: rest => do
    let some n := v.toNat? | throw "expected a node budget"
    options dump {o with limit := n} rest
  | flag :: v :: rest => do
    unless dump do throw usage
    match flag with
    | "--roots" => options dump {o with roots := ← names v} rest
    | "--full" => options dump {o with full := ← names v} rest
    | "--out" => options dump {o with out := v} rest
    | "--shard" =>
      let [a,b] := v.splitOn "/" | throw usage
      let some i := a.toNat? | throw usage
      let some n := b.toNat? | throw usage
      unless i < n do throw "invalid shard"
      options dump {o with shard := i, shards := n} rest
    | _ => throw usage
  | _ => throw usage

def report (env : Environment) (mod : Name) (target : Option Name) (b : Boundary)
    (o : Options') : Except String Json := do
  let g ← buildGraph env mod target b o.limit
  let j := (measurements g).setObjVal! "module" (toJson mod)
    |>.setObjVal! "target" (toJson target)
    |>.setObjVal! "boundary" (toJson (match b with | .decl => "decl" | .file => "file" | .module => "module"))
  unless o.graph do return j
  let nodes ← g.nodes.mapM fun node => do
    let json := toJson node
    if node.kind != "declLet" then return json
    let some mi := node.name.bind env.getModuleIdxFor? | throw "missing declaration owner"
    return json.setObjVal! "module" (toJson env.header.moduleNames[mi]!)
  return j.setObjVal! "graph" (.arr nodes)

def loadEnv (roots : Array Name) : IO Environment := do
  initSearchPath (← findSysroot)
  importModules (roots.map fun module => {module}) {}

def dump (o : Options') : IO UInt32 := do
  if o.roots.isEmpty then throw (IO.userError "--roots is required")
  let env ← loadEnv o.roots
  let prefixes := if o.full.isEmpty then o.roots else o.full
  IO.FS.createDirAll o.out
  let h ← IO.FS.Handle.mk (o.out / s!"decls.{o.shard}.jsonl") .write
  let mut failed := false
  for mi in [:env.header.moduleNames.size] do
    let mod := env.header.moduleNames[mi]!
    unless mi % o.shards == o.shard && prefixes.any (·.isPrefixOf mod) do continue
    for ci in env.header.moduleData[mi]!.constants do
      match report env mod ci.name .decl o with
      | .ok j => h.putStrLn j.compress
      | .error e =>
        h.putStrLn (Json.mkObj [("module", toJson mod), ("target", toJson ci.name), ("error", toJson e)]).compress
        failed := true
  h.flush
  return if failed then 1 else 0

def main (argv : List String) : IO UInt32 := do
  try
    if let "dump" :: rest := argv then return ← dump (← IO.ofExcept (options true {} rest))
    let cmd :: m :: rest := argv | throw (IO.userError usage)
    let (target, flags) := match rest with
      | n :: flags => if n.startsWith "--" then (none, rest) else (some n.toName, flags)
      | [] => (none, [])
    let b ← match cmd, target with
      | "decl", some _ => pure Boundary.decl
      | "file", none => pure Boundary.file
      | "module", _ => pure Boundary.module
      | _, _ => throw (IO.userError usage)
    let o ← IO.ofExcept (options false {} flags)
    let env ← loadEnv #[m.toName]
    let j ← IO.ofExcept (report env m.toName target b o)
    IO.println j.compress
    return 0
  catch e =>
    IO.eprintln e
    return 1
