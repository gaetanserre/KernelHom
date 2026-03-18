/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Lean.Elab.Tactic.Location
import LeanStoch.MonoidalComp.Quiver
import LeanStoch.MonoidalComp.MeasurableCoherence
import LeanStoch.Mathlib.MeasurableEquiv
import LeanStoch.Tactic.LocTactic
import LeanStoch.Tactic.Quiver.Universe
import LeanStoch.Tactic.Quiver.Utils
import Mathlib

import LeanStoch.Tactic.Quiver.KernelQuiver

open Lean Elab Tactic Meta CategoryTheory Parser.Tactic ProbabilityTheory MonoidalCategory

partial def get_type_from_Stoch (e : Expr) : MetaM (Expr × Level) := do
  let ewhnf ← whnf e
  match ewhnf.getAppFn with
  | Expr.const ``PUnit _ | Expr.const ``Unit _ =>
    return (Expr.const ``Unit [], Level.zero)
  | Expr.const ``Prod _ =>
    let args := ewhnf.getAppArgs
    let X := args[0]!
    let Y := args[1]!
    let (ex, xLevel) ← get_type_from_Stoch X
    let (ey, yLevel) ← get_type_from_Stoch Y
    let res ← mkAppOptM' (Expr.const ``Prod [xLevel, yLevel]) #[ex, ey]
    return (res, Level.max xLevel yLevel)
  | Expr.const ``ULift _ =>
    let args := ewhnf.getAppArgs
    let X := args[0]!
    return ← get_type_from_Stoch X
  | Expr.const ``MonoidalCategoryStruct.tensorUnit _ =>
    return (Expr.const ``Unit [], Level.zero)
  | Expr.const ``Stoch.of _ =>
    let args := ewhnf.getAppArgs
    if args.size < 1 then
      throwError "StochOf with insufficient arguments: {e}"
    else
      return ← get_type_from_Stoch args[0]!
  | _ =>
    match ← getLevel e with
    | Level.succ l => return (e, l)
    | _ => throwError "Expected a type with a universe level ≥ 0, got: {e}"

def deconstruct_unitors (iso : Expr) (maxLvl : Level) (left : Bool) :
    MetaM (Expr × MonoidalOP) := do
  let iso_t ← inferType iso
  let (X, xLevel) ← get_type_from_Stoch iso_t.getAppArgs[3]!
  let kernel_id ←
    if left then
      let UnitX ← mkAppOptM' (Expr.const ``Prod [Level.zero, xLevel]) #[Expr.const ``Unit [], X]
      let mUnitX ← synthInstance (mkApp (Expr.const ``MeasurableSpace [xLevel]) UnitX)
      mkAppOptM ``Kernel.id #[UnitX, mUnitX]
    else
      let XUnit ← mkAppOptM' (Expr.const ``Prod [xLevel, Level.zero]) #[X, Expr.const ``Unit []]
      let mXUnit ← synthInstance (mkApp (Expr.const ``MeasurableSpace [xLevel]) XUnit)
      mkAppOptM ``Kernel.id #[XUnit, mXUnit]
  let prod ← if left then
      mkAppOptM ``Prod.snd #[Expr.const ``Unit [], X]
    else
      mkAppOptM ``Prod.fst #[X, Expr.const ``Unit []]
  let ex ← construct_measurable_equiv X xLevel maxLvl
  let OP := if left then .leftUnitor (xLevel, ex) else .rightUnitor (xLevel, ex)
  return (← mkAppM ``Kernel.map #[kernel_id, prod], OP)

partial def transformQuiverToKernel (maxLvl : Level) (e : Expr) (op_data : List MonoidalOP) :
    MetaM (Expr × List MonoidalOP) := do
  match e.getAppFn with
  | Expr.const ``CategoryStruct.comp _ =>
    let args := e.getAppArgs
    let κ := args[args.size - 2]!
    let η := args[args.size - 1]!
    let (κ', lκ) ← transformQuiverToKernel maxLvl κ op_data
    let (η', lη) ← transformQuiverToKernel maxLvl η lκ
    return (← mkAppM ``Kernel.comp #[η', κ'], lη)
  | Expr.const ``monoidalComp _ =>
    let args := e.getAppArgs
    let κ := args[args.size - 2]!
    let η := args[args.size - 1]!
    let (κ', lκ) ← transformQuiverToKernel maxLvl κ op_data
    let (η', lη) ← transformQuiverToKernel maxLvl η lκ
    return (← mkAppOptM ``Kernel.monoComp
      #[none, none, none, none, none, none, none, none, none, κ', none, η', none], lη)
  | Expr.const ``Iso.hom _ =>
    let args := e.getAppArgs
    let iso := args[args.size - 1]!
    match iso.getAppFn with
    | Expr.const ``MonoidalCategoryStruct.leftUnitor _ =>
      let (res, leftUnitorOP) ← deconstruct_unitors iso maxLvl true
      logInfo m!"Constructed kernel for left unitor: {res}"
      return (res, leftUnitorOP :: op_data)
    | Expr.const ``MonoidalCategoryStruct.rightUnitor _ =>
      let (res, rightUnitorOP) ← deconstruct_unitors iso maxLvl false
      logInfo m!"Constructed kernel for right unitor: {res}"
      return (res, rightUnitorOP :: op_data)
    | _ => throwError "Expected a left unitor isomorphism, got: {iso}"
  | Expr.const ``Kernel.quiver _ =>
    logInfo m!"Transforming quiver expression: {e}"
    let args := e.getAppArgs
    let κ := args[args.size - 2]!
    logInfo m!"Extracted kernel expression: {κ}"
    return (κ, op_data)
  | _ => throwError "Expected a quiver expression, got: {e}"

def applyQuiverKernel (goal : MVarId) (fvarId : Option FVarId) : TacticM MVarId := do
  goal.withContext do
    let expr ← match fvarId with
        | some fid => do
          let decl ← fid.getDecl
          pure decl.type
        | none => goal.getType
    let maxLvl ← compute_max_universe (← collectKernelUniverses expr)
    let (quiverExpr, op_data, rhs, lhs) ← transformEquality maxLvl expr transformQuiverToKernel
    logInfo m!"Transformed expression: {quiverExpr}"
    throwError "This tactic is still under development and cannot be used yet."

syntax "quiver_kernel" (ppSpace location)? : tactic

elab_rules : tactic
  | `(tactic| quiver_kernel $[$loc]?) =>
    expandOptLocation (Lean.mkOptionalNode loc) |> applyLocTactic <| applyQuiverKernel

example {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] (κ : Kernel X Y)
    (η : Kernel Y Z) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    κ ⊗≫ₖ η = 0 := by
  kernel_quiver
  quiver_kernel

example {X : Type*} [MeasurableSpace X] :
    Kernel.id.map (Prod.snd : Unit × X → X) = (0 : Kernel (Unit × X) X) := by
  kernel_quiver
  quiver_kernel


example {X : Type*} [MeasurableSpace X] :
    Kernel.id.map (Prod.fst : X × Unit → X) = (0 : Kernel (X × Unit) X) := by
  kernel_quiver
  quiver_kernel
