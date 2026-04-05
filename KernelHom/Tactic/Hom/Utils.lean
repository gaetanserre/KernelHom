/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Lean
import Mathlib.Probability.Kernel.Basic

open Lean Meta ProbabilityTheory

/-!
# Kernel transformation utilities

This file provides helper functions for transforming between kernel expressions and
categorical morphism expressions, including type extraction and equivalence construction.

## Main declarations

- `get_types_from_kernel`: extracts carrier types and universe levels from kernel expressions.
- `construct_measurable_equiv`: recursively builds measurable equivalences.
- `transformEquality`: transforms an equality expression to an other using a provided
transformation function.
-/

/-- Extract `(X, Y, u, v)` from an expression of type `Kernel X Y`. -/
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

/-- Build a measurable equivalence for `e` into universe `maxLvl` (recursive on products). -/
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

/-- Pairing of a universe level with an expression used to record rewrite metadata. -/
abbrev LvlExpr := Level × Expr

/-- Categorical operations recorded during transformation for later rewriting. -/
inductive CategoryOP
  | leftUnitor (lvl_e : LvlExpr)
  | rightUnitor (lvl_e : LvlExpr)
  | WhiskerLeft (lvl_e : LvlExpr)
  | WhiskerRight (lvl_e : LvlExpr)
  | id (lvl_e : LvlExpr)

/-- Transform both sides of an equality and return the new equality plus metadata. -/
def transformEquality (maxLvl : Level) (e : Expr)
    (transform : Level → Expr → List CategoryOP → MetaM (Expr × List CategoryOP)) :
    MetaM (Expr × List CategoryOP × Expr × Expr) := do
  let e ← instantiateMVars e
  let e ← zetaReduce e
  let e ← whnf e
  let e := e.consumeMData
  match e with
  | Expr.app (Expr.app (Expr.app (Expr.const ``Eq _) _) lhsExpr) rhsExpr =>
    let (lhs, lh) ← transform maxLvl lhsExpr []
    let (rhs, rh) ← transform maxLvl rhsExpr lh
    return (← mkAppM `Eq #[lhs, rhs], rh, lhsExpr, rhsExpr)
  | _ =>
    throwError "Expected an equality, got: {e}"
