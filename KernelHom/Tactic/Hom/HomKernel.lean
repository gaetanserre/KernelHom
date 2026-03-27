/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Lean.Elab.Tactic.Location
import KernelHom.Hom
import KernelHom.MonoidalComp.MeasurableCoherence
import KernelHom.Mathlib.MeasurableEquiv
import KernelHom.Tactic.LocTactic
import KernelHom.Tactic.Hom.Universe
import KernelHom.Tactic.Hom.Utils

/-!
# `hom_kernel` tactic

This file implements the `hom_kernel` tactic, the inverse of `kernel_hom`.
It transforms equalities written in the monoidal category back into
equivalent equalities of kernels.

## Main declarations

- `transformHomToKernel`: recursive translation from categorical morphism expressions to
  kernel expressions.
- `mkHomKernelEqProof`: construction of the equivalence proof used by the
  tactic.
- `applyHomKernel`: core implementation on goals and hypotheses.
- `hom_kernel`: user-facing tactic (with location support).
-/

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
  | Expr.const ``SFinKer.of _ =>
    let args := ewhnf.getAppArgs
    if args.size < 1 then
      throwError "StochOf with insufficient arguments: {e}"
    else
      return ← get_type_from_Stoch args[0]!
  | _ =>
    match ← getLevel e with
    | Level.succ l => return (e, l)
    | _ => throwError "Expected a type with a universe level ≥ 0, got: {e}"

def deconstruct_unitors (iso : Expr) (eLevel : Level) (left : Bool) :
    MetaM (Expr × CategoryOP) := do
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
  let ex ← construct_measurable_equiv X xLevel eLevel
  let OP := if left then .leftUnitor (xLevel, ex) else .rightUnitor (xLevel, ex)
  return (← mkAppM ``Kernel.map #[kernel_id, prod], OP)

def deconstruct_whiskers_args (e : Expr) (eLevel : Level) (left : Bool) :
    MetaM (Expr × Expr × CategoryOP) := do
  let args := e.getAppArgs
  let SX := if left then args[args.size - 4]! else args[args.size - 1]!
  let κ := if left then args[args.size - 1]! else args[args.size - 2]!
  let (X, xLevel) ← get_type_from_Stoch SX
  let mXUnit ← synthInstance (mkApp (Expr.const ``MeasurableSpace [xLevel]) X)
  let kernel_id ← mkAppOptM ``Kernel.id #[X, mXUnit]
  let exEquiv ← construct_measurable_equiv X xLevel eLevel
  let OP := if left then .WhiskerLeft (xLevel, exEquiv) else .WhiskerRight (xLevel, exEquiv)
  return (κ, kernel_id, OP)

partial def transformHomToKernel (eLevel : Level) (e : Expr) (op_data : List CategoryOP) :
    MetaM (Expr × List CategoryOP) := do
  match e.getAppFn with
  | Expr.const ``CategoryStruct.id _ =>
    let args := e.getAppArgs
    let X := args[args.size - 1]!
    let (X', xLevel) ← get_type_from_Stoch X
    let ex ← construct_measurable_equiv X' xLevel eLevel
    let mX' ← synthInstance (mkApp (Expr.const ``MeasurableSpace [xLevel]) X')
    return (← mkAppOptM ``Kernel.id #[X', mX'], .id (xLevel, ex) :: op_data)
  | Expr.const ``CategoryStruct.comp _ =>
    let args := e.getAppArgs
    let κ := args[args.size - 2]!
    let η := args[args.size - 1]!
    let (κ', lκ) ← transformHomToKernel eLevel κ op_data
    let (η', lη) ← transformHomToKernel eLevel η lκ
    return (← mkAppM ``Kernel.comp #[η', κ'], lη)
  | Expr.const ``monoidalComp _ =>
    let args := e.getAppArgs
    let κ := args[args.size - 2]!
    let η := args[args.size - 1]!
    let (κ', lκ) ← transformHomToKernel eLevel κ op_data
    let (η', lη) ← transformHomToKernel eLevel η lκ
    return (← mkAppOptM ``Kernel.monoComp
      #[none, none, none, none, none, none, none, none, none, κ', none, η', none], lη)
  | Expr.const ``Iso.hom _ =>
    let args := e.getAppArgs
    let iso := args[args.size - 1]!
    match iso.getAppFn with
    | Expr.const ``MonoidalCategoryStruct.leftUnitor _ =>
      let (res, leftUnitorOP) ← deconstruct_unitors iso eLevel true
      return (res, leftUnitorOP :: op_data)
    | Expr.const ``MonoidalCategoryStruct.rightUnitor _ =>
      let (res, rightUnitorOP) ← deconstruct_unitors iso eLevel false
      return (res, rightUnitorOP :: op_data)
    | _ => throwError "Expected a left unitor isomorphism, got: {iso}"
  | Expr.const ``MonoidalCategoryStruct.whiskerLeft _ =>
    let (κ, kernel_id, whiskerLeftOP) ← deconstruct_whiskers_args e eLevel true
    let (κ', lκ) ← transformHomToKernel eLevel κ op_data
    let res ← mkAppM ``Kernel.parallelComp #[kernel_id, κ']
    return (res, whiskerLeftOP :: lκ)
  | Expr.const ``MonoidalCategoryStruct.whiskerRight _ =>
    let (κ, kernel_id, whiskerRightOP) ← deconstruct_whiskers_args e eLevel false
    let (κ', lκ) ← transformHomToKernel eLevel κ op_data
    let res ← mkAppM ``Kernel.parallelComp #[κ', kernel_id]
    return (res, whiskerRightOP :: lκ)
  | Expr.const ``Kernel.hom _ =>
    let args := e.getAppArgs
    let κ := args[args.size - 2]!
    return (κ, op_data)
  | _ => throwError "Expected a hom expression, got: {e}"

def mkHomKernelEqProof (eqProofType : Expr) (eLevel : Level)
    (op_data : List CategoryOP) : TacticM Expr := do
  let eLevelStx ← liftMacroM <| levelToSyntax eLevel
  let savedGoals ← getGoals
  let mvar ← mkFreshExprSyntheticOpaqueMVar eqProofType
  let mvarId := mvar.mvarId!
  setGoals [mvarId]
  evalTactic (← `(tactic| apply propext))
  evalTactic (← `(tactic| constructor))
  let goalsAfterConstructor ← getGoals
  match goalsAfterConstructor with
  | [forwardGoal, backwardGoal] =>
    setGoals [forwardGoal]
    evalTactic (← `(tactic| intro h))
    evalTactic (← `(tactic| try dsimp only [MonoidalCategoryStruct.tensorUnit,
      MonoidalCategoryStruct.tensorObj] at h))
    for e in op_data do
      match e with
      | .leftUnitor (_, expr) =>
        let eStx ← Term.exprToSyntax expr
        evalTactic (← `(tactic| try rw [Kernel.leftUnitor.{$eLevelStx, _, 0}
          (ex := $eStx)] at h))
      | .rightUnitor (_, expr) =>
        let eStx ← Term.exprToSyntax expr
        evalTactic (← `(tactic| try rw [Kernel.rightUnitor.{$eLevelStx, _, 0}
          (ex := $eStx)] at h))
      | .id (_, expr) =>
        let eStx ← Term.exprToSyntax expr
        evalTactic (← `(tactic| try rw [Kernel.quiver_id.{$eLevelStx} (ex := $eStx)] at h))
      | _ => pure ()
    let congr_tac ← `(tactic| first
      | simp only [
        Kernel.quiver_monoComp.{$eLevelStx},
        Kernel.quiver_comp.{$eLevelStx},
      ] at h
      | simp only [
        Kernel.quiver_comp.{$eLevelStx},
      ] at h
    )
    try
      evalTactic congr_tac
    catch _ =>
      pure ()
    for e in op_data do
      match e with
      | .WhiskerLeft (_, expr) =>
        let eStx ← Term.exprToSyntax expr
        evalTactic (← `(tactic| rw [Kernel.WhiskerLeft.{$eLevelStx} (ez := $eStx)] at h))
      | .WhiskerRight (_, expr) =>
        let eStx ← Term.exprToSyntax expr
        evalTactic (← `(tactic| rw [Kernel.WhiskerRight.{$eLevelStx} (ez := $eStx)] at h))
      | _ => pure ()
    try
      evalTactic congr_tac
    catch _ =>
      pure ()
    evalTactic (← `(tactic| rwa [Kernel.quiver_congr.{$eLevelStx}] at h))

    setGoals [backwardGoal]
    evalTactic (← `(tactic| intro h))
    evalTactic (← `(tactic| try dsimp only [MonoidalCategoryStruct.tensorUnit,
      MonoidalCategoryStruct.tensorObj]))
    for e in op_data do
      match e with
      | .leftUnitor (_, expr) =>
        let eStx ← Term.exprToSyntax expr
        evalTactic (← `(tactic| try rw [Kernel.leftUnitor.{$eLevelStx, _, 0} (ex := $eStx)]))
      | .rightUnitor (_, expr) =>
        let eStx ← Term.exprToSyntax expr
        evalTactic (← `(tactic| try rw [Kernel.rightUnitor.{$eLevelStx, _, 0} (ex := $eStx)]))
      | .id (_, expr) =>
        let eStx ← Term.exprToSyntax expr
        evalTactic (← `(tactic| try rw [Kernel.quiver_id.{$eLevelStx} (ex := $eStx)]))
      | _ => pure ()
    let congr_tac ← `(tactic| first
      | simp only [
        Kernel.quiver_monoComp.{$eLevelStx},
        Kernel.quiver_comp.{$eLevelStx},
      ]
      | simp only [
        Kernel.quiver_comp.{$eLevelStx},
      ]
    )
    try
      evalTactic congr_tac
    catch _ =>
      pure ()
    for e in op_data do
      match e with
      | .WhiskerLeft (_, expr) =>
        let eStx ← Term.exprToSyntax expr
        evalTactic (← `(tactic| rw [Kernel.WhiskerLeft.{$eLevelStx} (ez := $eStx)]))
      | .WhiskerRight (_, expr) =>
        let eStx ← Term.exprToSyntax expr
        evalTactic (← `(tactic| rw [Kernel.WhiskerRight.{$eLevelStx} (ez := $eStx)]))
      | _ => pure ()
    try
      evalTactic congr_tac
    catch _ =>
      pure ()
    evalTactic (← `(tactic| rwa [Kernel.quiver_congr.{$eLevelStx}]))
  | _ =>
    setGoals savedGoals
    throwError "Expected exactly two goals after `constructor`"
  if !(← getGoals).isEmpty then
    setGoals savedGoals
    throwError "Failed to solve all goals while building kernel_hom equivalence proof"

  setGoals savedGoals
  instantiateMVars mvar

def applyHomKernel (goal : MVarId) (fvarId : Option FVarId) : TacticM MVarId := do
  goal.withContext do
    let expr ← match fvarId with
        | some fid => do
          let decl ← fid.getDecl
          pure decl.type
        | none => goal.getType
    let eLevel ← get_universe_from_cat_eq expr
    let (quiverExpr, op_data, _, _) ← transformEquality eLevel expr transformHomToKernel
    let eqProofType ← mkEq expr quiverExpr
    let eqProof ← mkHomKernelEqProof eqProofType eLevel op_data
    match fvarId with
    | some fid => do
      let mvarId ← getMainGoal
      let hProof ← mkEqMP eqProof (mkFVar fid)
      let userName := (← fid.getDecl).userName
      let mvarId ← mvarId.assert userName quiverExpr hProof
      let mvarId ← mvarId.tryClear fid
      let (_, mvarId) ← mvarId.intro1P
      pure mvarId
    | none => do
      let mvarId ← getMainGoal
      mvarId.replaceTargetEq quiverExpr eqProof

syntax "hom_kernel" (ppSpace location)? : tactic

/-- The `hom_kernel` tactic is the inverse of `kernel_hom`: it transforms an
equality written in the monoidal category back to an equivalent equality of
s-finite kernels.

The tactic supports location specifiers like `rw` or `simp`:
- `hom_kernel` — applies to the goal
- `hom_kernel at h` — applies to hypothesis `h`
- `hom_kernel at h₁ h₂` — applies to multiple hypotheses
- `hom_kernel at h ⊢` — applies to hypothesis `h` and the goal
- `hom_kernel at *` — applies to all hypotheses and the goal

It is useful to switch back to kernel equations once categorical rewrites are done. -/
elab_rules : tactic
  | `(tactic| hom_kernel $[$loc]?) =>
    expandOptLocation (Lean.mkOptionalNode loc) |> applyLocTactic <| applyHomKernel
