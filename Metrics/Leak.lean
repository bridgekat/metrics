import Lean

/-!
# The definitional-leak test

Whether a proof depends on what a definition *is* rather than on what was proved about it. The
proof term of a theorem is re-checked (by `Meta.check`, at default transparency) with definitions
from other modules made irreducible. If the check passes as written and fails once a definition is
sealed, the proof unfolds that definition silently: by applying a hypothesis of a defined
proposition as a function, by an anonymous constructor, by `show`/`change`/`exact` up to
definitional equality, by `rfl`. Rewriting with the definition's equation lemma does not count
here: that leaves the lemma's name in the term, and is counted from the term.

This is the mechanical form of the API rubric's test, "try to use the new API without unfolding".
-/

open Lean Meta

namespace Metrics

/-- Whether a theorem's proof term is type correct, and has the stated type, without unfolding
anything irreducible. -/
def checkUnit (ci : ConstantInfo) : MetaM Bool := do
  let some v := ci.value? (allowOpaque := true) | return true
  try
    Meta.check v .default
    let t ← inferType v
    withTransparency .default <| isDefEq t ci.type
  catch _ => return false

inductive LeakOutcome where
  /-- The proof does not check even as written (or runs out of budget): no verdict. -/
  | noControl
  /-- It checks with every candidate sealed. -/
  | clean
  /-- It fails with all candidates sealed; these fail on their own. Empty when only a
  combination fails. -/
  | leaks (ds : Array Name)

/--
Run the test on one theorem against the candidate definitions. Each check runs from the pristine
environment with fresh caches, since sealing a definition invalidates them.
-/
def leakTest (env : Environment) (ctx : Core.Context) (ci : ConstantInfo) (cands : Array Name) :
    IO LeakOutcome := do
  let run (sealed : Array Name) : IO Bool := do
    try
      let x : CoreM Bool := withCurrHeartbeats do
        for d in sealed do setIrreducibleAttribute d
        (checkUnit ci).run'
      let (ok, _) ← x.toIO ctx { env }
      pure ok
    catch _ => pure false
  unless ← run #[] do return .noControl
  if ← run cands then return .clean
  let mut ds := #[]
  for d in cands do
    unless ← run #[d] do ds := ds.push d
  return .leaks ds

end Metrics
