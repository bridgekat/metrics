import Metrics.Analyze
import Metrics.Replace
import Metrics.Leak

/-!
# metrics

`metrics dump` imports a project's modules and writes, for every declaration of the selected
modules, the record of `Metrics.analyze`. See the README.
-/

open Lean Meta Metrics

structure Args where
  roots : Array Name := #[]
  /-- Module-name prefixes whose declarations get full records. -/
  full : Array Name := #[]
  /-- Module-name prefixes whose declarations get statement hashes only. -/
  stmt : Array Name := #[]
  /-- Module-name prefixes whose theorems are glue rather than lemmas. -/
  glue : Array Name := #[`Init, `Std, `Lean, `Batteries, `Aesop, `Qq, `Plausible, `ProofWidgets,
    `Mathlib.Tactic, `Mathlib.Logic, `Mathlib.Util, `Mathlib.Lean, `Mathlib.Init, `Mathlib.Order.Defs]
  out : System.FilePath := "metrics-out"
  shard : Nat := 0
  shards : Nat := 1
  /-- Of the `full` modules matching `samplePrefix`, keep one in this many. -/
  sample : Nat := 1
  samplePrefix : Name := `Mathlib
  minFp : Nat := 3
  /-- `replace`: candidates applied per theorem, `solve_by_elim` depth, heartbeats (thousands). -/
  maxCand : Nat := 300
  depth : Nat := 4
  heartbeats : Nat := 400000
  verbose : Bool := false

def parseNames (s : String) : Array Name :=
  (s.splitOn ",").toArray.filterMap fun p => if p.isEmpty then none else some p.toName

partial def parseArgs (a : Args) : List String → Except String Args
  | [] => pure a
  | "--roots" :: v :: rest => parseArgs { a with roots := parseNames v } rest
  | "--full" :: v :: rest => parseArgs { a with full := parseNames v } rest
  | "--stmt" :: v :: rest => parseArgs { a with stmt := parseNames v } rest
  | "--glue" :: v :: rest => parseArgs { a with glue := parseNames v } rest
  | "--out" :: v :: rest => parseArgs { a with out := v } rest
  | "--shard" :: v :: rest =>
    match v.splitOn "/" with
    | [i, n] => parseArgs { a with shard := i.toNat!, shards := n.toNat! } rest
    | _ => throw s!"--shard wants i/n, got {v}"
  | "--sample" :: v :: rest => parseArgs { a with sample := v.toNat! } rest
  | "--sample-prefix" :: v :: rest => parseArgs { a with samplePrefix := v.toName } rest
  | "--min-fp" :: v :: rest => parseArgs { a with minFp := v.toNat! } rest
  | "--max-cand" :: v :: rest => parseArgs { a with maxCand := v.toNat! } rest
  | "--depth" :: v :: rest => parseArgs { a with depth := v.toNat! } rest
  | "--verbose" :: rest => parseArgs { a with verbose := true } rest
  | "--heartbeats" :: v :: rest => parseArgs { a with heartbeats := v.toNat! } rest
  | x :: _ => throw s!"unknown argument {x}"

/-- Whether a name is compiler-generated. A private name is judged without its prefix. -/
def internalName (n : Name) : Bool := ((privateToUserName? n).getD n).isInternalDetail

def hasPrefix (ps : Array Name) (m : Name) : Bool := ps.any (·.isPrefixOf m)

def runCore (env : Environment) (x : CoreM α) : IO α := do
  let ctx : Core.Context := {
    fileName := "<metrics>", fileMap := default, maxHeartbeats := 0, maxRecDepth := 100000 }
  return (← x.toIO ctx { env }).1

unsafe def importRoots (a : Args) : IO Environment := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let t0 ← IO.monoMsNow
  let env ← importModules (a.roots.map fun r => { module := r }) {} (trustLevel := 1024)
    (loadExts := true)
  IO.eprintln s!"imported {a.roots} in {(← IO.monoMsNow) - t0} ms \
    ({env.header.moduleNames.size} modules)"
  IO.FS.createDirAll a.out
  return env

/-- Whether module `mi` is one whose declarations this run measures in full. -/
def Args.isFull (a : Args) (m : Name) : Bool :=
  hasPrefix a.full m &&
    (a.sample ≤ 1 || !a.samplePrefix.isPrefixOf m || (hash m).toNat % a.sample == 0)

unsafe def dump (a : Args) : IO Unit := do
  let env ← importRoots a
  let t1 ← IO.monoMsNow
  let mods := env.header.moduleNames
  -- the constants: ids, and which theorems count as lemmas
  let mut cid : Std.HashMap Name Nat := {}
  let mut lemmaKind : Std.HashMap Name UInt8 := {}
  let mut aux : Std.HashSet Name := {}
  let mut neutral : Std.HashSet Name := {}
  let mut total := 0
  for mi in [0:mods.size] do
    let glue := hasPrefix a.glue mods[mi]!
    let md := env.header.moduleData[mi]!
    for ci in md.constants do
      let n := ci.name
      cid := cid.insert n total
      total := total + 1
      if ci matches .thmInfo _ then
        -- a theorem that is an instance, or that produces one, is plumbing rather than a step
        let producesInst := match ci.type.getForallBody.getAppFn with
          | .const k _ => isClass env k
          | _ => false
        lemmaKind := lemmaKind.insert n
          (if glue || producesInst || isInstanceCore env n then 1 else 2)
        if let .str _ s := n then
          if s.startsWith "_" then aux := aux.insert n
      if isMatcherCore env n || isAuxRecursor env n || isNoConfusion env n then
        neutral := neutral.insert n
  if a.shard == 0 then
    let simp := simpExtension.getState env
    let hm ← IO.FS.Handle.mk (a.out / "modules.tsv") .write
    for mi in [0:mods.size] do hm.putStrLn s!"{mi}\t{mods[mi]!}"
    let hc ← IO.FS.Handle.mk (a.out / "consts.tsv") .write
    let mut id := 0
    for mi in [0:mods.size] do
      let md := env.header.moduleData[mi]!
      for ci in md.constants do
        let n := ci.name
        let red := match getReducibilityStatusCore env n with
          | .reducible => "r" | .irreducible => "x" | _ => "s"
        let flags := s!"{if isInstanceCore env n then "I" else ""}\
          {if isClass env n then "C" else ""}\
          {if isStructure env n then "S" else ""}\
          {if simp.lemmaNames.contains (.decl n) then "s" else ""}\
          {if isPrivateName n then "p" else ""}\
          {if internalName n then "x" else ""}\
          {if env.isProjectionFn n then "j" else ""}\
          {if isMatcherCore env n then "m" else ""}\
          {if lemmaKind.getD n 0 == 1 then "g" else ""}\
          {if Linter.isDeprecated env n then "D" else ""}"
        hc.putStrLn s!"{id}\t{n}\t{kindChar ci}\t{mi}\t{red}\t{flags}"
        id := id + 1
    IO.eprintln s!"wrote {total} constants"
  let cfg : Cfg := { env, lemmaKind, cid, minFp := a.minFp, aux, neutral }
  let r ← R.new
  let h ← IO.FS.Handle.mk (a.out / s!"decls.{a.shard}.jsonl") .write
  let mut done := 0
  let mut errs := 0
  for mi in [0:mods.size] do
    let m := mods[mi]!
    if mi % a.shards != a.shard then continue
    let isFull := a.isFull m
    unless isFull || hasPrefix a.stmt m do continue
    let md := env.header.moduleData[mi]!
    for ci in md.constants do
      let n := ci.name
      -- auxiliary constants are read through the declarations that use them
      if internalName n then continue
      -- statement-only records are for comparing statements: skip what nobody states
      if !isFull && !(ci matches .thmInfo _ | .defnInfo _) then continue
      let res ← try
          let (fields, rng, doc) ← runCore env do
            let fields ← (analyze cfg r ci isFull).run'
            let rng ← findDeclarationRanges? n
            let doc ← findDocString? env n
            return (fields, rng, doc)
          let mut fs := #[s!"\"i\":{cid[n]!}", s!"\"f\":{if isFull then 1 else 0}"]
          if let some rg := rng then
            fs := fs.push s!"\"l0\":{rg.range.pos.line},\"l1\":{rg.range.endPos.line}"
          if doc.isSome then fs := fs.push "\"doc\":1"
          pure (some (fs ++ fields))
        catch e =>
          IO.eprintln s!"error on {n}: {e}"
          pure none
      match res with
      | some fs => h.putStrLn ("{" ++ ",".intercalate fs.toList ++ "}")
      | none => errs := errs + 1
      done := done + 1
    if mi % 200 == 0 then
      IO.eprintln s!"[{a.shard}] module {mi}/{mods.size}, {done} records, {(← IO.monoMsNow) - t1} ms"
  h.flush
  IO.eprintln s!"[{a.shard}] done: {done} records, {errs} errors, {(← IO.monoMsNow) - t1} ms"

/--
`metrics replace`: for every written theorem of the selected modules, the replaceability test of
`Metrics.tryReplace`. One JSON line per theorem: its id, the lemma that closes it if any, the
number of candidates tried, and the time.
-/
unsafe def replace (a : Args) : IO Unit := do
  let env ← importRoots a
  let t1 ← IO.monoMsNow
  let mods := env.header.moduleNames
  let mut cid : Std.HashMap Name Nat := {}
  let mut total := 0
  for mi in [0:mods.size] do
    for ci in env.header.moduleData[mi]!.constants do
      cid := cid.insert ci.name total
      total := total + 1
  -- where each project declaration is, to order them: a candidate must come before its target
  let project (m : Name) : Bool := hasPrefix a.roots m
  let mut pos : Std.HashMap Name (Nat × Nat) := {}
  for mi in [0:mods.size] do
    unless project mods[mi]! || a.isFull mods[mi]! do continue
    for ci in env.header.moduleData[mi]!.constants do
      let n := ci.name
      let rng ← runCore env (findDeclarationRanges? n)
      pos := pos.insert n (mi, (rng.map (·.range.pos.line)).getD 1000000000)
  IO.eprintln s!"[{a.shard}] located {pos.size} declarations, {(← IO.monoMsNow) - t1} ms"
  -- library search indexes the imported constants on first use; do that outside any budget
  let _ ← runCore env (LibrarySearch.libSearchFindDecls (mkConst ``True)).run'
  IO.eprintln s!"[{a.shard}] indexed the library, {(← IO.monoMsNow) - t1} ms"
  let h ← IO.FS.Handle.mk (a.out / s!"replace.{a.shard}.jsonl") .write
  let ctx : Core.Context := {
    fileName := "<metrics>", fileMap := default, maxHeartbeats := a.heartbeats * 1000,
    maxRecDepth := 100000 }
  let mut done := 0
  let mut hits := 0
  let mut k := 0
  for mi in [0:mods.size] do
    let m := mods[mi]!
    unless a.isFull m do continue
    for ci in env.header.moduleData[mi]!.constants do
      let n := ci.name
      unless ci matches .thmInfo _ do continue
      if internalName n || Linter.isDeprecated env n then continue
      -- a theorem that is an instance, or that produces one, is found by instance resolution,
      -- not by name: it is not what this test is about
      if isInstanceCore env n then continue
      if let .const cls _ := ci.type.getForallBody.getAppFn then
        if isClass env cls then continue
      let some (_, line) := pos[n]? | continue
      if line == 1000000000 then continue
      k := k + 1
      if k % a.shards != a.shard then continue
      let admissible (c : Name) : Bool :=
        c != n && !internalName c && !n.isPrefixOf c &&
          match pos[c]? with
          | some (cm, cl) => cm < mi || (cm == mi && cl < line)
          | none => true
      let t ← IO.monoMsNow
      if a.verbose then IO.eprintln s!"[{a.shard}] {n}"
      let res ← try
          let x : CoreM _ := withCurrHeartbeats ((tryReplace n admissible a.maxCand a.depth).run')
          let (r, _) ← x.toIO ctx { env }
          pure (some r)
        catch _ => pure none
      let ms := (← IO.monoMsNow) - t
      match res with
      | some (some { byRfl := true, .. }, _) =>
        h.putStrLn s!"\{\"i\":{cid[n]!},\"rfl\":1,\"ms\":{ms}}"
      | some (some r, tried) =>
        hits := hits + 1
        h.putStrLn s!"\{\"i\":{cid[n]!},\"hit\":{(cid[r.lemma]?).getD 0},\"dir\":\"{r.dir}\",\
          \"tried\":{tried},\"ms\":{ms}}"
      | some (none, tried) => h.putStrLn s!"\{\"i\":{cid[n]!},\"tried\":{tried},\"ms\":{ms}}"
      | none => h.putStrLn s!"\{\"i\":{cid[n]!},\"err\":1,\"ms\":{ms}}"
      done := done + 1
      if done % 20 == 0 then h.flush
      if done % 500 == 0 then
        IO.eprintln s!"[{a.shard}] {done} theorems, {hits} hits, {(← IO.monoMsNow) - t1} ms"
  h.flush
  IO.eprintln s!"[{a.shard}] done: {done} theorems, {hits} hits, {(← IO.monoMsNow) - t1} ms"

/--
`metrics leak`: for every theorem of the selected modules (auxiliary ones included, since that is
where tactic blocks end up), the definitional-leak test of `Metrics.leakTest` against the
definitions of the same library that it mentions. One JSON line
per theorem that mentions any: its id, the candidates, and the outcome.
-/
unsafe def leak (a : Args) : IO Unit := do
  let env ← importRoots a
  let t1 ← IO.monoMsNow
  let mods := env.header.moduleNames
  let mut cid : Std.HashMap Name Nat := {}
  let mut total := 0
  -- the definitions worth sealing: plain `def`s a reader would call definitions
  let mut sealable : Std.HashMap Name Nat := {}
  for mi in [0:mods.size] do
    for ci in env.header.moduleData[mi]!.constants do
      let n := ci.name
      cid := cid.insert n total
      total := total + 1
      if ci matches .defnInfo _ then
        if !internalName n && !isInstanceCore env n && !env.isProjectionFn n &&
            !isMatcherCore env n && !isAuxRecursor env n && !isNoConfusion env n &&
            (getReducibilityStatusCore env n matches .semireducible) then
          sealable := sealable.insert n mi
  -- a definition is a candidate for the theorems of its own library; the project is one library
  -- (for another library, its top-level area: `Mathlib.Analysis`, `Mathlib.Topology`, ...)
  let lib (m : Name) : Name :=
    if hasPrefix a.roots m then `_project
    else match m.components with
      | a :: b :: _ => a ++ b
      | _ => m.getRoot
  let h ← IO.FS.Handle.mk (a.out / s!"leak.{a.shard}.jsonl") .write
  let ctx : Core.Context := {
    fileName := "<metrics>", fileMap := default, maxHeartbeats := a.heartbeats * 1000,
    maxRecDepth := 100000 }
  let mut done := 0
  let mut k := 0
  let mut nleak := 0
  for mi in [0:mods.size] do
    let m := mods[mi]!
    unless a.isFull m do continue
    for ci in env.header.moduleData[mi]!.constants do
      let n := ci.name
      unless ci matches .thmInfo _ do continue
      let some v := ci.value? (allowOpaque := true) | continue
      k := k + 1
      if k % a.shards != a.shard then continue
      let used := (v.getUsedConstantsAsSet).insertMany ci.type.getUsedConstantsAsSet
      let cands := used.toArray.filter fun d =>
        match sealable[d]? with
        | some dm => lib mods[dm]! == lib m
        | none => false
      if cands.isEmpty then continue
      -- a proof that mentions very many definitions is tested against the first ones only
      let cands := cands.qsort (fun x y => cid[x]! < cid[y]!) |>.extract 0 a.maxCand
      let t ← IO.monoMsNow
      let out ← leakTest env ctx ci cands
      let ms := (← IO.monoMsNow) - t
      let cs := ",".intercalate (cands.toList.map fun d => toString cid[d]!)
      let res := match out with
        | .noControl => "\"ctl\":0"
        | .clean => "\"ctl\":1,\"leaks\":[]"
        | .leaks ds => "\"ctl\":1,\"sealed_fails\":1,\"leaks\":[" ++
            ",".intercalate (ds.toList.map fun d => toString cid[d]!) ++ "]"
      if out matches .leaks _ then nleak := nleak + 1
      h.putStrLn s!"\{\"i\":{cid[n]!},\"c\":[{cs}],{res},\"ms\":{ms}}"
      done := done + 1
      if done % 500 == 0 then
        h.flush
        IO.eprintln s!"[{a.shard}] {done} theorems, {nleak} leaking, {(← IO.monoMsNow) - t1} ms"
  h.flush
  IO.eprintln s!"[{a.shard}] done: {done} theorems, {nleak} leaking, {(← IO.monoMsNow) - t1} ms"

unsafe def main (argv : List String) : IO UInt32 := do
  match argv with
  | "leak" :: rest =>
    match parseArgs {} rest with
    | .ok a => leak a; return 0
    | .error e => IO.eprintln e; return 2
  | "dump" :: rest =>
    match parseArgs {} rest with
    | .ok a => dump a; return 0
    | .error e => IO.eprintln e; return 2
  | "replace" :: rest =>
    match parseArgs {} rest with
    | .ok a => replace a; return 0
    | .error e => IO.eprintln e; return 2
  | _ =>
    IO.eprintln "usage: metrics dump --roots A,B --full A,B [--stmt Mathlib] --out DIR \
      [--shard i/n] [--sample k] [--min-fp k] [--glue P,Q]"
    return 2
