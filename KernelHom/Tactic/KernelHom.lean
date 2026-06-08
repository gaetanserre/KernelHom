/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import KernelHom.Kernel.Hom
public import KernelHom.Tactic.Utils
public import KernelHom.ForMathlib.MeasurableEquiv
public import Lean.Elab.Tactic.Location
public import KernelLift.Tactic.KernelLift

/-!
# `kernel_hom` tactic

This file implements the `kernel_hom` tactic, which transforms equalities of
kernels into equivalent equalities in the monoidal category.

## Main declarations

* `transformKernelToHom`: recursive translation from kernel expressions to
  categorical morphism expressions.
* `mkKernelHomEqProof`: construction of the equivalence proof used by the
  tactic.
* `applyKernelHom`: core implementation of `kernel_hom` on goals and hypotheses.
* `kernel_hom`: user-facing tactic (with location support).
-/

public meta section

open Lean Elab Tactic Meta CategoryTheory Parser.Tactic ProbabilityTheory MonoidalCategory
open ProbabilityTheory.Kernel

/-- Recursive transformation from kernel expressions to morphism expressions in the `SFinKer`
category. -/
partial def transformKernelToHom (e : Expr) (op_data : List CategoryOP) :
    MetaM (Expr × List CategoryOP) := do
  match e.getAppFn with
  | _ =>
    let (X, Y, _, _) ← getTypesFromKernel e
    let ex ← mkAppOptM ``MeasurableEquiv.id #[X, none]
    let ey ← mkAppOptM ``MeasurableEquiv.id #[Y, none]
    let SX ← mkAppOptM ``SFinKer.of #[X, none]
    let SY ← mkAppOptM ``SFinKer.of #[Y, none]
    let homExpr ← mkAppOptM ``ProbabilityTheory.Kernel.hom
      #[X, Y, none, none, SX, SY, ex, ey, e, none]
    pure (homExpr, op_data)

/-- Construct the proof of equivalence between the original equality and the transformed one. -/
def mkKernelHomEqProof (eqProofType : Expr) (op_data : List CategoryOP) : TacticM Expr := do
  let savedGoals ← getGoals
  let mvar ← mkFreshExprSyntheticOpaqueMVar eqProofType
  let mvarId := mvar.mvarId!
  setGoals [mvarId]
  let op_data := op_data.reverse
  evalTactic (← `(tactic| apply propext))
  evalTactic (← `(tactic| rw [hom_congr]))
  evalTactic (← `(tactic| constructor))
  let goalsAfterConstructor ← getGoals
  match goalsAfterConstructor with
  | [forwardGoal, backwardGoal] =>
    setGoals [forwardGoal]
    evalTactic (← `(tactic| intro h))
    evalTactic (← `(tactic| kernel_lift at h))
    evalTactic (← `(tactic| exact h))

    setGoals [backwardGoal]
    evalTactic (← `(tactic| intro h))
    evalTactic (← `(tactic| kernel_lift))
    evalTactic (← `(tactic| exact h))
  | _ =>
    setGoals savedGoals
    throwError "Expected exactly two goals after `constructor`"
  if !(← getGoals).isEmpty then
    setGoals savedGoals
    throwError "Failed to solve all goals while building kernel_hom equivalence proof"
  setGoals savedGoals
  instantiateMVars mvar

/-- The `kernel_hom` tactic transforms a kernel equality to an equivalent equality in
the category of measurable spaces and s-finite kernels.

The tactic supports location specifiers like `rw` or `simp`:
* `kernel_hom` — applies to the goal
* `kernel_hom at h` — applies to hypothesis `h`
* `kernel_hom at h₁ h₂` — applies to multiple hypotheses
* `kernel_hom at h ⊢` — applies to hypothesis `h` and the goal
* `kernel_hom at *` — applies to all hypotheses and the goal

Example:
```lean
example {W X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    [MeasurableSpace W] (κ : Kernel X Y) (η : Kernel Y Z) (ξ : Kernel Z W)
    [IsFiniteKernel ξ] [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    ξ ∘ₖ (η ∘ₖ κ) = ξ ∘ₖ η ∘ₖ κ := by
  kernel_hom
  exact Category.assoc _ _ _
``` -/
def ApplyKernelHom (goal : MVarId) (fvarId : Option FVarId) : TacticM MVarId := do
  goal.withContext do
    let expr ← match fvarId with
        | some fid => do
          let decl ← fid.getDecl
          pure decl.type
        | none => goal.getType
    let expr ← whnfR <| ← unfoldKernelOp <| ← instantiateMVars expr
    let (lifted_expr, _, _) ← LiftEquality expr
    logInfo m!"Original expression: {expr}"
    logInfo m!"Lifted expression: {lifted_expr}"
    let (homExpr, op_data, rhs, lhs) ← transformEquality lifted_expr CategoryOP transformKernelToHom
    logInfo m!"Transformed expression: {homExpr}"
    let eqProofType ← mkEq expr homExpr
    logInfo m!"Equivalence proof type: {eqProofType}"
    let eqProof ← mkKernelHomEqProof eqProofType op_data
    match fvarId with
    | some fid => do
      let mvarId ← getMainGoal
      let hProof ← mkEqMP eqProof (mkFVar fid)
      let userName := (← fid.getDecl).userName
      let mvarId ← mvarId.assert userName homExpr hProof
      let mvarId ← mvarId.tryClear fid
      let (_, mvarId) ← mvarId.intro1P
      pure mvarId
    | none => do
      let mvarId ← getMainGoal
      mvarId.replaceTargetEq homExpr eqProof
    /- let maxLvl ← computeMaxUniverse (← collectExprUniverses expr)
    let (homExpr, op_data, rhs, lhs) ← transformEquality maxLvl expr transformKernelToHom
    let eqProofType ← mkEq expr homExpr
    let eqProof ← mkKernelHomEqProof eqProofType rhs lhs maxLvl op_data
    match fvarId with
    | some fid => do
      let mvarId ← getMainGoal
      let hProof ← mkEqMP eqProof (mkFVar fid)
      let userName := (← fid.getDecl).userName
      let mvarId ← mvarId.assert userName homExpr hProof
      let mvarId ← mvarId.tryClear fid
      let (_, mvarId) ← mvarId.intro1P
      pure mvarId
    | none => do
      let mvarId ← getMainGoal
      mvarId.replaceTargetEq homExpr eqProof -/

@[inherit_doc ApplyKernelHom]
syntax (name := kernelHom) "kernel_hom" (ppSpace location)? : tactic

elab_rules : tactic
  | `(tactic| kernel_hom $[$loc]?) =>
    expandOptLocation (Lean.mkOptionalNode loc) |> applyLocTactic <| ApplyKernelHom

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (κ : Kernel X Y) [IsSFiniteKernel κ]

example : κ = κ := by
  kernel_hom
  rfl
