import Metrics.Basic

/-!
# Structural hashes

`hashE` hashes a term so that two terms agree when they differ only in what a reader would not
call a difference: binder names and kinds, universe levels, metadata, and (optionally) the
instance arguments. Free variables hash to whatever the caller says, which is how the statement
hashes of `Metrics.Analyze` are made independent of the order of hypotheses.
-/

open Lean Meta

namespace Metrics

/-- The parameters of a structural hash. -/
structure HCtx where
  env : Environment
  r : R
  /-- Hash every instance-implicit argument as one constant, unless it involves a chosen
  instance. -/
  eraseInst : Bool
  /-- The hash of each free variable; one not listed hashes as `kFree`. -/
  fvh : Std.HashMap FVarId H

/-- Whether an instance argument involves a chosen instance (see `R.isChosenInst`). -/
partial def chosenInst (env : Environment) (r : R) (e : Expr) : BaseIO Bool := do
  let e := e.consumeMData
  let .const h _ := e.getAppFn | return false
  if ← r.isChosenInst env h then return true
  let bis ← r.getBinfo env h
  let args := e.getAppArgs
  for i in [0:args.size] do
    if (bis.getD i .default).isInstImplicit then
      if ← chosenInst env r args[i]! then return true
  return false

mutual

/-- A structural hash: binder names, binder kinds, universe levels and metadata do not count. -/
unsafe def hashE (hc : HCtx) (e : Expr) : BaseIO H := do
  match e with
  | .bvar i => return mx kBVar (hash i)
  | .sort _ => return kSort
  | .lit l => return mx kLit (hash l)
  | .mvar _ => return kFree
  | .const n _ => return mx kConst (hash n)
  | .fvar id => return hc.fvh.getD id kFree
  | .mdata _ b => hashE hc b
  | _ =>
    let key := ptrAddrUnsafe e
    if let some v := (← hc.r.hmemo.get)[key]? then return v
    let v ← hashCore hc e
    hc.r.hmemo.modify (·.insert key v)
    return v

unsafe def hashCore (hc : HCtx) (e : Expr) : BaseIO H := do
  match e with
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    let mut h := mx kApp (← hashE hc f)
    let mask ← match f with
      | .const n _ => if hc.eraseInst then hc.r.getBinfo hc.env n else pure #[]
      | _ => pure #[]
    for i in [0:args.size] do
      let ha ← if (mask.getD i .default).isInstImplicit &&
          !(← chosenInst hc.env hc.r args[i]!) then pure kInst else hashE hc args[i]!
      h := mx h ha
    return h
  | .lam _ t b _ => return mx kLam (mx (← hashE hc t) (← hashE hc b))
  | .forallE _ t b _ => return mx kPi (mx (← hashE hc t) (← hashE hc b))
  | .letE _ t v b _ => return mx kLet (mx (← hashE hc t) (mx (← hashE hc v) (← hashE hc b)))
  | .proj s i b => return mx (mx kProj (hash s)) (mx (hash i) (← hashE hc b))
  | _ => return kFree

end

/-- Hash a proposition so that the two sides of an equation, an equivalence or a disequation may
be swapped, also under quantifiers and negation. -/
unsafe def hashSym (hc : HCtx) (e : Expr) : BaseIO H := do
  let e := e.consumeMData
  match e with
  | .forallE _ t b _ => return mx kPi (mx (← hashE hc t) (← hashSym hc b))
  | _ =>
    let f := e.getAppFn
    let args := e.getAppArgs
    let sym (k : H) (a b : Expr) : BaseIO H := do
      let ha ← hashE hc a
      let hb ← hashE hc b
      return mx k (mx (min ha hb) (max ha hb))
    match f, args.size with
    | .const ``Eq _, 3 => sym (mx kConst (hash ``Eq)) args[1]! args[2]!
    | .const ``Ne _, 3 => sym (mx kConst (hash ``Ne)) args[1]! args[2]!
    | .const ``Iff _, 2 => sym (mx kConst (hash ``Iff)) args[0]! args[1]!
    | .const ``Not _, 1 => return mx (mx kConst (hash ``Not)) (← hashSym hc args[0]!)
    | _, _ => hashE hc e

/-- Hash with a fresh memo: the memo is only valid for one choice of `fvh` and `eraseInst`. -/
unsafe def hashFresh (hc : HCtx) (e : Expr) : BaseIO H := do
  hc.r.hmemo.set {}
  hashE hc e

/-- `hashSym` with a fresh memo. -/
unsafe def hashSymFresh (hc : HCtx) (e : Expr) : BaseIO H := do
  hc.r.hmemo.set {}
  hashSym hc e

end Metrics
