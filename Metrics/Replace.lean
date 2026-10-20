import Lean

/-!
# The replaceability test

Whether a theorem's statement is closed by a single application of a lemma that existed before it,
with the hypotheses discharged from the context: what `exact?` would find at the moment the theorem
was stated. This is the mechanical form of the reuse rubric's blocking condition, "a new
declaration that a located existing declaration directly replaces".

The candidates are the library-search matches of the conclusion (and of its symmetric form). A
candidate from the project counts only if it is declared earlier, in the order of modules and
lines, so that of two equivalent theorems only the later one is reported and no theorem is
"replaced" by a consequence of itself.
-/

open Lean Meta

namespace Metrics

structure ReplaceResult where
  /-- The lemma that closes the statement. -/
  lemma : Name
  /-- `mp`/`mpr` when one direction of an equivalence was used. -/
  dir : String
  /-- How many candidates were applied before it. -/
  tried : Nat
  /-- The statement holds by reflexivity: no lemma is involved, it is a definitional restatement. -/
  byRfl : Bool := false

def dirString : LibrarySearch.DeclMod → String
  | .none => ""
  | .mp => "mp"
  | .mpr => "mpr"

/--
Try to close the statement of `declName` by one admissible lemma and `solve_by_elim`.
Returns the lemma, or `none` with the number of candidates tried.
-/
def tryReplace (declName : Name) (admissible : Name → Bool) (maxCand : Nat) (depth : Nat) :
    MetaM (Option ReplaceResult × Nat) := do
  let ci ← getConstInfo declName
  forallTelescope ci.type fun _ concl => do
    let s0 ← saveState
    let byRfl ← try
        (← mkFreshExprMVar concl).mvarId!.applyRfl
        pure true
      catch _ => pure false
    restoreState s0
    if byRfl then return (some { lemma := .anonymous, dir := "", tried := 0, byRfl := true }, 0)
    let goal := (← mkFreshExprMVar concl).mvarId!
    let cands ← LibrarySearch.librarySearchSymm LibrarySearch.libSearchFindDecls goal
    let s ← saveState
    let mut tried := 0
    for ((g, mctx), (name, mod)) in cands do
      unless admissible name do continue
      if tried ≥ maxCand then break
      tried := tried + 1
      let ok ← try
          setMCtx mctx
          let lem ← LibrarySearch.mkLibrarySearchLemma name mod
          let newGoals ← g.apply lem { allowSynthFailures := false }
          let rest ← LibrarySearch.solveByElim [] (exfalso := false) newGoals (maxDepth := depth)
          pure rest.isEmpty
        catch _ => pure false
      restoreState s
      if ok then return (some { lemma := name, dir := dirString mod, tried }, tried)
    return (none, tried)

end Metrics
