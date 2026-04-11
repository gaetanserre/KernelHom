/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Lean
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Composition.CompProd

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

open Lean Meta ProbabilityTheory

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

/-- Categorical operations recorded during transformation for later rewriting. -/
inductive CategoryOP
  | leftUnitor_hom (lvl : Level) (e : Expr)
  | leftUnitor_inv (lvl : Level) (e : Expr)
  | rightUnitor_hom (lvl : Level) (e : Expr)
  | rightUnitor_inv (lvl : Level) (e : Expr)
  | WhiskerLeft (e : Expr)
  | WhiskerRight (e : Expr)
  | id (e : Expr)
  | Associator_hom (e₁ e₂ e₃ : Expr)
  | Associator_inv (e₁ e₂ e₃ : Expr)
  | Braiding_hom (e₁ e₂ : Expr)
  | Counit (e : Expr)
  | Comul (e : Expr)

/-- Transform both sides of an equality and return the new equality plus metadata. -/
def transformEquality (maxLvl : Level) (e : Expr)
    (transform : Level → Expr → List CategoryOP → MetaM (Expr × List CategoryOP)) :
    MetaM (Expr × List CategoryOP × Expr × Expr) := do
  let e ← instantiateMVars e
  let e ← zetaReduce e
  let e ← whnf e
  let e := e.consumeMData
  let some (_, lhs, rhs) := e.eq? | throwError "Expected an equality, got: {e}"
  let (lhs', lh) ← transform maxLvl lhs []
  let (rhs', rh) ← transform maxLvl rhs lh
  return (← mkAppM `Eq #[lhs', rhs'], rh, lhs, rhs)

/-- Unfold kernel operations in an expression. -/
def unfold_kernel_op (e : Expr) : MetaM Expr := do
  let names := (.empty |> NameSet.insert <| ``Kernel.prod) |> NameSet.insert <| ``Kernel.compProd
  transform e (post := fun e => do
    let e' ← deltaExpand e names.contains
    let e' ← Core.betaReduce e'
    return .done e')
