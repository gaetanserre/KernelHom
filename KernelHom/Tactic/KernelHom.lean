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

/-- Recursively decompose a product type into `SFinKer` objects with monoidal tensor structure. -/
partial def decomposeProductToSFinker (X : Expr) (xLvl : Level) : MetaM Expr := do
  let whnfX ← whnf X
  match whnfX.getAppFn with
  | Expr.const ``Prod _ =>
    let args := whnfX.getAppArgs
    let a1 := args[0]!
    let t1 ← mkAppOptM ``SFinKer.of #[a1, none]
    let t2 ← decomposeProductToSFinker args[1]! xLvl
    mkAppM ``tensorObj #[t1, t2]
  | _ =>
    mkAppOptM ``SFinKer.of #[X, none]

/-- Compute the `SFinKer` object corresponding to a measurable space. -/
def computeSFinkerOf (X : Expr) (xLvl : Level) : MetaM Expr := do
  match ← whnf X with
  | Expr.const ``PUnit _ | Expr.const ``Unit _ =>
    let tensorunit :=
      Expr.const ``tensorUnit [xLvl, xLvl.succ]
    let sfinker := Expr.const ``SFinKer [xLvl]
    mkAppOptM' tensorunit #[sfinker, none, none]
  | _ =>
    decomposeProductToSFinker X xLvl

partial def idME (X : Expr) : MetaM Expr := do
  let whnfX ← whnf X
  match whnfX.getAppFn with
  | Expr.const ``Prod _ =>
    let args := whnfX.getAppArgs
    let id1 ← idME args[0]!
    let id2 ← idME args[1]!
    mkAppM ``MeasurableEquiv.prod #[id1, id2]
  | _ =>
    mkAppOptM ``MeasurableEquiv.id #[X, none]

/-- Recursive transformation from kernel expressions to morphism expressions in the `SFinKer`
category. -/
partial def transformKernelToHom (e : Expr) (op_data : List CategoryOP) :
    MetaM (Expr × List CategoryOP) := do
  match e.getAppFn with
  | Expr.const ``Kernel.comp _ =>
    let args := e.getAppArgs
    let η := args[args.size - 2]!
    let κ := args[args.size - 1]!
    let (X, Y, xLvl, yLvl) ← getTypesFromKernel η
    let (Z, _, tLvl, _) ← getTypesFromKernel κ
    let SX ← computeSFinkerOf X xLvl
    let SY ← computeSFinkerOf Y yLvl
    let SZ ← computeSFinkerOf Z tLvl
    let OPComp := .Comp (← idME X) SX (← idME Y) SY (← idME Z) SZ
    let (κ', lκ') ← transformKernelToHom κ op_data
    let (η', lη') ← transformKernelToHom η lκ'
    return (← mkAppM ``CategoryStruct.comp #[κ', η'], OPComp :: lη')
  | Expr.const ``Kernel.parallelComp _ =>
    let args := e.getAppArgs
    let κ := args[args.size - 2]!
    let η := args[args.size - 1]!
    let (X, Y, xLvl, yLvl) ← getTypesFromKernel κ
    let (Z, T, zLvl, tLvl) ← getTypesFromKernel η
    let SX ← computeSFinkerOf X xLvl
    let SY ← computeSFinkerOf Y yLvl
    let SZ ← computeSFinkerOf Z zLvl
    let ST ← computeSFinkerOf T tLvl
    let OPParallelComp :=
      .ParallelComp (← idME X) SX (← idME Y) SY (← idME Z) SZ (← idME T) ST
    let (κ', lκ') ← transformKernelToHom κ op_data
    let (η', lη') ← transformKernelToHom η lκ'
    return (← mkAppM ``tensorHom #[κ', η'], OPParallelComp :: lη')
  | Expr.const ``Kernel.id [xLvl] =>
    let X := e.getAppArgs[0]!
    let SX ← computeSFinkerOf X xLvl
    let OPId := .Id (← idME X) SX
    logInfo m!"{OPId}"
    return (← mkAppM ``CategoryStruct.id #[SX], OPId :: op_data)
  | _ =>
    let (X, Y, xLvl, yLvl) ← getTypesFromKernel e
    let SX ← computeSFinkerOf X xLvl
    let SY ← computeSFinkerOf Y yLvl
    let homExpr ← mkAppOptM ``ProbabilityTheory.Kernel.hom
      #[X, Y, none, none, SX, SY, (← idME X), (← idME Y), e, none]
    pure (homExpr, op_data)

/-- Construct the proof of equivalence between the original equality and the transformed one. -/
def mkKernelHomEqProof (eqProofType : Expr) (op_data : List CategoryOP) : TacticM Expr := do
  let savedGoals ← getGoals
  let mvar ← mkFreshExprSyntheticOpaqueMVar eqProofType
  let mvarId := mvar.mvarId!
  setGoals [mvarId]
  let op_data := op_data.reverse
  evalTactic (← `(tactic| apply propext))
  for op in op_data do
    match op with
    | .Comp ex SX ey SY ez SZ =>
      let terms ← exprsToSyntax #[ex, SX, ey, SY, ez, SZ]
      evalTactic (← `(tactic| nth_rw 1 [
        comp_hom
        (ex := $(terms[0]!))
        (SX := $(terms[1]!))
        (ey := $(terms[2]!))
        (SY := $(terms[3]!))
        (ez := $(terms[4]!))
        (SZ := $(terms[05]!))
      ]))
    | .ParallelComp ex SX ey SY ez SZ et ST =>
      let terms ← exprsToSyntax #[ex, SX, ey, SY, ez, SZ, et, ST]
      evalTactic (← `(tactic| nth_rw 1 [
        parallelComp_hom
        (ex := $(terms[0]!))
        (SX := $(terms[1]!))
        (ey := $(terms[2]!))
        (SY := $(terms[3]!))
        (ez := $(terms[4]!))
        (SZ := $(terms[5]!))
        (et := $(terms[6]!))
        (ST := $(terms[7]!))
      ]))
    | .Id ex SX =>
      let terms ← exprsToSyntax #[ex, SX]
      evalTactic (← `(tactic| nth_rw 1 [
        id_hom
        (ex := $(terms[0]!))
        (SX := $(terms[1]!))
      ]))
  evalTactic (← `(tactic| rw [hom_congr]))
  /- evalTactic (← `(tactic| constructor))
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
    throwError "Expected exactly two goals after `constructor`" -/
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

    /- Decide wether we need to lift the kernel expression to a homogeneous universe level first.
    If this is necessary, we also need to construct the proof of equivalence between the original
    expression and the lifted one, which will be used later to construct the final equivalence
    proof. -/
    let (lifted_expr, constructLiftedProof) ← do
      let result ← (LiftEquality expr).run
      match result with
      | Except.error .AlreadyHomogeneous =>
        pure (expr, (fun e ↦ pure e))
      | Except.ok (lifted_expr, kernel_op_data, maxLvl) =>
        let liftedProofType ← mkEq expr lifted_expr
        let liftedEqProof ← mkKernelLiftEqProof liftedProofType maxLvl kernel_op_data
        pure (lifted_expr, (fun e ↦ mkEqTrans liftedEqProof e))

    let (homExpr, op_data, _, _) ← transformEquality lifted_expr CategoryOP transformKernelToHom
    logInfo m!"Original expression: {expr}"
    logInfo m!"Lifted expression: {lifted_expr}"
    logInfo m!"Hom expression: {homExpr}"

    let homEqProofType ← mkEq lifted_expr homExpr
    logInfo m!"Equivalence proof type: {homEqProofType}"
    let homEqProof ← mkKernelHomEqProof homEqProofType op_data

    let EqProof ← constructLiftedProof homEqProof
    match fvarId with
    | some fid => do
      let mvarId ← getMainGoal
      let hProof ← mkEqMP EqProof (mkFVar fid)
      let userName := (← fid.getDecl).userName
      let mvarId ← mvarId.assert userName homExpr hProof
      let mvarId ← mvarId.tryClear fid
      let (_, mvarId) ← mvarId.intro1P
      pure mvarId
    | none => do
      let mvarId ← getMainGoal
      mvarId.replaceTargetEq homExpr EqProof

@[inherit_doc ApplyKernelHom]
syntax (name := kernelHom) "kernel_hom" (ppSpace location)? : tactic

elab_rules : tactic
  | `(tactic| kernel_hom $[$loc]?) =>
    expandOptLocation (Lean.mkOptionalNode loc) |> applyLocTactic <| ApplyKernelHom

variable {X Y Z T : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  [MeasurableSpace T]

variable (κ : Kernel X Y) [IsSFiniteKernel κ] (η : Kernel Y Z) [IsSFiniteKernel η]

example : Kernel.id (α := (X × Y)) = (0 : Kernel (X × Y) (X × Y)) := by
  kernel_hom
  sorry
