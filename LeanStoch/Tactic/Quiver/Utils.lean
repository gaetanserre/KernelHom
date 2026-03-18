/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Lean
import Mathlib.Probability.Kernel.Basic

open Lean Meta ProbabilityTheory

def get_types_from_kernel (κ : Expr) : MetaM (Expr × Expr × Level × Level) := do
  let κType ← inferType κ
  match κType.getAppFn with
  | Expr.const ``Kernel univs =>
    let args := κType.getAppArgs
    if args.size < 2 then
      throwError "Kernel type with insufficient arguments: {κType}"
    let X := args[0]!
    let Y := args[1]!
    let xLevel := univs[0]!
    let yLevel := univs[1]!
    return (X, Y, xLevel, yLevel)
  | _ => throwError "Expected a kernel type, got: {κType}"

partial def construct_measurable_equiv (e : Expr) (eLevel maxLvl : Level) : MetaM Expr := do
  let ewhnf ← whnf e
  match ewhnf.getAppFn with
  | Expr.const ``PUnit _ | Expr.const ``Unit _ =>
    mkAppOptM' (Expr.const `MeasurableEquiv.punit [maxLvl, eLevel]) #[]
  | Expr.const ``Prod univs =>
    let args := ewhnf.getAppArgs
    let X := args[0]!
    let Y := args[1]!
    let xLevel := univs[0]!
    let yLevel := univs[1]!
    let ex ← construct_measurable_equiv X xLevel maxLvl
    let ey ← construct_measurable_equiv Y yLevel maxLvl
    let res ← mkAppOptM' (Expr.const `MeasurableEquiv.prod [maxLvl, xLevel, yLevel])
      #[none, none, none, none, none, none, none, none, ex, ey]
    return res
  | _ => mkAppOptM' (Expr.const `MeasurableEquiv.ulift [eLevel, maxLvl]) #[e, none]

abbrev LvlExpr := Level × Expr

inductive MonoidalOP
  | leftUnitor (lvl_e : LvlExpr)
  | rightUnitor (lvl_e : LvlExpr)
  | WhiskerLeft (lvl_e : LvlExpr)
  | WhiskerRight (lvl_e : LvlExpr)

def transformEquality (maxLvl : Level) (e : Expr)
    (transform : Level → Expr → List MonoidalOP → MetaM (Expr × List MonoidalOP)) :
    MetaM (Expr × List MonoidalOP × Expr × Expr) := do
  if e.isAppOfArity `Eq 3 then
    let (lhs, lh) ← transform maxLvl e.getAppArgs[1]! []
    let (rhs, rh) ← transform maxLvl e.getAppArgs[2]! lh
    return (← mkAppM `Eq #[lhs, rhs], rh, e.getAppArgs[1]!, e.getAppArgs[2]!)
  else
    throwError "Expected an equality, got: {e}"
