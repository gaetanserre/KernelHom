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
# `kernel_hom` tactic

This file implements the `kernel_hom` tactic, which transforms equalities of
kernels into equivalent equalities in the monoidal category.

## Main declarations

- `transformKernelToHom`: recursive translation from kernel expressions to
  categorical morphism expressions.
- `mkKernelHomEqProof`: construction of the equivalence proof used by the
  tactic.
- `applyKernelHom`: core implementation on goals and hypotheses.
- `kernel_hom`: user-facing tactic (with location support).
-/

open Lean Elab Tactic Meta CategoryTheory Parser.Tactic ProbabilityTheory MonoidalCategory

def check_unitors (κ : Expr) (offset : Nat) (prod : Name) : MetaM Bool := do
  let κ := κ.consumeMData
  if !κ.getAppFn.isConstOf ``Kernel.map then
    return false
  let args := κ.getAppArgs
  let fn := args[args.size - 1]!
  let idKernel := args[args.size - 2]!
  if !fn.getAppFn.isConstOf prod then
    return false
  if !idKernel.getAppFn.isConstOf ``Kernel.id then
    return false
  let (src, _, _) ← get_types_from_kernel κ
  let srcWhnf ← whnf src
  match srcWhnf.getAppFn with
  | Expr.const ``Prod _ =>
    let args := srcWhnf.getAppArgs
    if args.size < 2 then
      return false
    let punit? := args[offset]!
    match punit?.getAppFn with
    | Expr.const ``PUnit _ | Expr.const ``Unit _ => return true
    | _ => return false
  | _ => return false

def check_leftUnitor (κ : Expr) : MetaM Bool := check_unitors κ 0 ``Prod.snd

def check_rightUnitor (κ : Expr) : MetaM Bool := check_unitors κ 1 ``Prod.fst

def compute_StochOf (X : Expr) (xLevel maxLvl : Level) : MetaM Expr := do
  match ← whnf X with
  | Expr.const ``PUnit _ | Expr.const ``Unit _ =>
    let sfinker := Expr.const `SFinKer [maxLvl]
    let tensorunit :=
      Expr.const ``MonoidalCategoryStruct.tensorUnit [maxLvl, maxLvl.succ]
    mkAppOptM' tensorunit #[sfinker, none, none]
  | _ =>
    let ex ← inferType (← construct_measurable_equiv X xLevel maxLvl)
    let lifted_X := ex.getAppArgs[0]!
    let stochOfconst := Expr.const `SFinKer.of [maxLvl]
    mkAppOptM' stochOfconst #[lifted_X, none]

def construct_unitors (X Y : Expr) (yLvl maxLvl : Level) (offset : Nat) :
  MetaM (Expr × CategoryOP) := do
  let left ← if offset == 0 then pure true
    else if offset == 1 then pure false
    else throwError "Invalid offset for unitors"
  let punit_level ← match (← whnf X).getAppFn with
  | Expr.const ``Prod univs => pure univs[offset]!
  | _ =>
    if left then throwError "Expected left unitor with source PUnit × X, got: {X}"
    else throwError "Expected right unitor with source X × PUnit, got: {X}"
  let stochOf ← compute_StochOf Y yLvl maxLvl
  let unitor ← if left then mkAppM ``MonoidalCategoryStruct.leftUnitor #[stochOf]
    else mkAppM ``MonoidalCategoryStruct.rightUnitor #[stochOf]
  let ey ← construct_measurable_equiv Y yLvl maxLvl
  let unitorOP := if left then .leftUnitor (punit_level, ey)
    else .rightUnitor (punit_level, ey)
  return (← mkAppM ``Iso.hom #[unitor], unitorOP)

def check_Whiskers (κ : Expr) (offset : Nat) : MetaM Bool := do
  let κ := κ.consumeMData
  if !κ.getAppFn.isConstOf ``Kernel.parallelComp then
    return false
  let args := κ.getAppArgs
  let idKernel := args[args.size - offset]!
  if !idKernel.getAppFn.isConstOf ``Kernel.id then
    return false
  else return true

def check_WhiskerLeft (κ : Expr) : MetaM Bool := check_Whiskers κ 2

def check_WhiskerRight (κ : Expr) : MetaM Bool := check_Whiskers κ 1

def construct_whiskers_args (e X : Expr) (maxLvl : Level) (offset : Nat) :
    MetaM (Expr × Expr × Expr × Level) := do
  let left ← if offset == 0 then pure true
    else if offset == 1 then pure false
    else throwError "Invalid offset for whiskers"
  let whnfX ← whnf X
  let (Z, zLvl) ← match whnfX.getAppFn with
  | Expr.const ``Prod univs =>
    let args := whnfX.getAppArgs
    pure (args[offset]!, univs[offset]!)
  | _ =>
    if left then throwError "Expected left whisker with source Z × X, got: {X}"
    else throwError "Expected right whisker with source X × Z, got: {X}"
  let stochOfZ ← compute_StochOf Z zLvl maxLvl
  let κ ← match e.getAppFn with
    | Expr.const ``Kernel.parallelComp _ =>
      let args := e.getAppArgs
      pure args[args.size - (offset + 1)]!
    | _ =>
      if left then throwError "Expected left whisker with parallelComp, got: {e}"
      else throwError "Expected right whisker with parallelComp, got: {e}"
  return (stochOfZ, κ, Z, zLvl)

/-- Transform a kernel expression to its morphism representation with explicit universe level. -/
partial def transformKernelToHom (maxLvl : Level) (e : Expr) (op_data : List CategoryOP) :
    MetaM (Expr × List CategoryOP) := do
  match e.getAppFn with
  | Expr.const ``Kernel.comp _ =>
    let args := e.getAppArgs
    let κ := args[args.size - 2]!
    let η := args[args.size - 1]!
    let (η', lη) ← transformKernelToHom maxLvl η op_data
    let (κ', lκ) ← transformKernelToHom maxLvl κ lη
    return (← mkAppM ``CategoryStruct.comp #[η', κ'], lκ)
  | Expr.const ``Kernel.monoComp _ =>
    let args := e.getAppArgs
    let κ := args[args.size - 4]!
    let η := args[args.size - 2]!
    let (_, X, _, xLevel) ← get_types_from_kernel κ
    let (Y, _, yLevel, _) ← get_types_from_kernel η
    let (κ', lκ) ← transformKernelToHom maxLvl κ op_data
    let (η', lη) ← transformKernelToHom maxLvl η lκ
    let ex ← construct_measurable_equiv X xLevel maxLvl
    let ey ← construct_measurable_equiv Y yLevel maxLvl
    let monoComp := Expr.const ``monoidalComp [maxLvl, maxLvl.succ]
    let monoCoherenceConst := Expr.const `MeasurableCoherence.monoidalCoherence
      [maxLvl, xLevel, yLevel]
    let monoCoherence ← mkAppOptM' monoCoherenceConst
      #[none, none, none, none, none, none, none, none, none, ex, ey]
    return (← mkAppOptM' monoComp
      #[none, none, none, none, none, none, monoCoherence, κ', η'], lη)
  | Expr.const ``Kernel.id univs =>
    let args := e.getAppArgs
    let X := args[args.size - 2]!
    let xLevel := univs[0]!
    let stochOfX ← compute_StochOf X xLevel maxLvl
    let ex ← construct_measurable_equiv X xLevel maxLvl
    let idOP := .id (xLevel, ex)
    return (← mkAppM ``CategoryStruct.id #[stochOfX], idOP :: op_data)
  | _ =>
    let (X, Y, xLevel, yLevel) ← get_types_from_kernel e
    if ← check_leftUnitor e then
      let (leftUnitorExpr, leftUnitorOP) ← construct_unitors X Y yLevel maxLvl 0
      return (leftUnitorExpr, leftUnitorOP :: op_data)
    else if ← check_rightUnitor e then
      let (rightUnitorExpr, rightUnitorOP) ← construct_unitors X Y yLevel maxLvl 1
      return (rightUnitorExpr, rightUnitorOP :: op_data)
    else if ← check_WhiskerLeft e then
      let (stochOfZ, κ, Z, zLvl) ← construct_whiskers_args e X maxLvl 0
      let (κ', lκ) ← transformKernelToHom maxLvl κ op_data
      let whiskerleft ← mkAppM ``MonoidalCategoryStruct.whiskerLeft #[stochOfZ, κ']
      let ez ← construct_measurable_equiv Z zLvl maxLvl
      let leftWhiskerOP := .WhiskerLeft (zLvl, ez)
      return (whiskerleft, leftWhiskerOP :: lκ)
    else if ← check_WhiskerRight e then
      let (stochOfZ, κ, Z, zLvl) ← construct_whiskers_args e X maxLvl 1
      let (κ', lκ) ← transformKernelToHom maxLvl κ op_data
      let whiskerleft ← mkAppM ``MonoidalCategoryStruct.whiskerRight #[κ', stochOfZ]
      let ez ← construct_measurable_equiv Z zLvl maxLvl
      let rightWhiskerOP := .WhiskerRight (zLvl, ez)
      return (whiskerleft, rightWhiskerOP :: lκ)
    else
      let quiverConst := Expr.const ``Kernel.hom [maxLvl, xLevel, yLevel]
      let ex ← construct_measurable_equiv X xLevel maxLvl
      let ey ← construct_measurable_equiv Y yLevel maxLvl
      return( ← mkAppOptM' quiverConst
        #[none, none, none, none, none, none, none, none, ex, ey, e, none], op_data)

def mkKernelHomEqProof (eqProofType rhs lhs : Expr) (maxLvl : Level)
    (op_data : List CategoryOP) : TacticM Expr := do
  let maxLevelStx ← liftMacroM <| levelToSyntax maxLvl
  let rhsStx ← Term.exprToSyntax rhs
  let lhsStx ← Term.exprToSyntax lhs
  let op_data := op_data.reverse
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
    evalTactic (← `(tactic| try dsimp only [MonoidalCategoryStruct.tensorUnit]))
    for e in op_data do
      match e with
      | .leftUnitor (lvl, equiv) =>
        let punitLevelStx ← liftMacroM <| levelToSyntax lvl
        let eStx ← Term.exprToSyntax equiv
        evalTactic (← `(tactic| nth_rw 1 [Kernel.leftUnitor.{$maxLevelStx, _, $punitLevelStx}
          (ex := $eStx)]))
      | .rightUnitor (lvl, equiv) =>
        let punitLevelStx ← liftMacroM <| levelToSyntax lvl
        let eStx ← Term.exprToSyntax equiv
        evalTactic (← `(tactic| nth_rw 1 [Kernel.rightUnitor.{$maxLevelStx, _, $punitLevelStx}
          (ex := $eStx)]))
      | .id (_, equiv) =>
        let eStx ← Term.exprToSyntax equiv
        evalTactic (← `(tactic| rw [Kernel.quiver_id.{$maxLevelStx} (ex := $eStx)]))
      | _ => pure ()
    let congr_tac ← `(tactic| first
      | simp only [
        Kernel.quiver_monoComp.{$maxLevelStx},
        Kernel.quiver_comp.{$maxLevelStx},
      ]
      | simp only [
        Kernel.quiver_comp.{$maxLevelStx},
      ]
    )
    try
      evalTactic congr_tac
    catch _ =>
      pure ()
    for e in op_data do
      match e with
      | .WhiskerLeft (_, equiv) =>
        let eStx ← Term.exprToSyntax equiv
        evalTactic (← `(tactic| nth_rw 1 [Kernel.WhiskerLeft.{$maxLevelStx} (ez := $eStx)]))
      | .WhiskerRight (_, equiv) =>
        let eStx ← Term.exprToSyntax equiv
        evalTactic (← `(tactic| nth_rw 1 [Kernel.WhiskerRight.{$maxLevelStx} (ez := $eStx)]))
      | _ => pure ()
    try
      evalTactic congr_tac
    catch _ =>
      pure ()
    evalTactic (← `(tactic| rwa [Kernel.quiver_congr.{$maxLevelStx}
      (κ₁ := $rhsStx) (κ₂ := $lhsStx)]))

    setGoals [backwardGoal]
    evalTactic (← `(tactic| intro h))
    evalTactic (← `(tactic| try dsimp only [MonoidalCategory.tensorUnit] at h))
    for e in op_data do
      match e with
      | .leftUnitor (lvl, equiv) =>
        let punitLevelStx ← liftMacroM <| levelToSyntax lvl
        let eStx ← Term.exprToSyntax equiv
        evalTactic (← `(tactic| nth_rw 1 [Kernel.leftUnitor.{$maxLevelStx, _, $punitLevelStx}
          (ex := $eStx)] at h))
      | .rightUnitor (lvl, equiv) =>
        let punitLevelStx ← liftMacroM <| levelToSyntax lvl
        let eStx ← Term.exprToSyntax equiv
        evalTactic (← `(tactic| nth_rw 1 [Kernel.rightUnitor.{$maxLevelStx, _, $punitLevelStx}
          (ex := $eStx)] at h))
      | .id (_, equiv) =>
        let eStx ← Term.exprToSyntax equiv
        evalTactic (← `(tactic| rw [Kernel.quiver_id.{$maxLevelStx} (ex := $eStx)] at h))
      | _ => pure ()
    let congr_tac ← `(tactic| first
      | simp only [
        Kernel.quiver_monoComp.{$maxLevelStx},
        Kernel.quiver_comp.{$maxLevelStx},
      ] at h
      | simp only [
        Kernel.quiver_comp.{$maxLevelStx},
      ] at h
    )
    try
      evalTactic congr_tac
    catch _ =>
      pure ()
    for e in op_data do
      match e with
      | .WhiskerLeft (_, equiv) =>
        let eStx ← Term.exprToSyntax equiv
        evalTactic (← `(tactic| nth_rw 1 [Kernel.WhiskerLeft.{$maxLevelStx} (ez := $eStx)] at h))
      | .WhiskerRight (_, equiv) =>
        let eStx ← Term.exprToSyntax equiv
        evalTactic (← `(tactic| nth_rw 1 [Kernel.WhiskerRight.{$maxLevelStx} (ez := $eStx)] at h))
      | _ => pure ()
    try
      evalTactic congr_tac
    catch _ =>
      pure ()
    evalTactic (← `(tactic| rwa [Kernel.quiver_congr.{$maxLevelStx} (κ₁ := $rhsStx)
      (κ₂ := $lhsStx)] at h))
  | _ =>
    setGoals savedGoals
    throwError "Expected exactly two goals after `constructor`"

  if !(← getGoals).isEmpty then
    setGoals savedGoals
    throwError "Failed to solve all goals while building kernel_hom equivalence proof"

  setGoals savedGoals
  instantiateMVars mvar

def applyKernelHom (goal : MVarId) (fvarId : Option FVarId) : TacticM MVarId := do
  goal.withContext do
    let expr ← match fvarId with
        | some fid => do
          let decl ← fid.getDecl
          pure decl.type
        | none => goal.getType
    let maxLvl ← compute_max_universe (← collectExprUniverses expr)
    let (quiverExpr, op_data, rhs, lhs) ← transformEquality maxLvl expr transformKernelToHom
    let eqProofType ← mkEq expr quiverExpr
    let eqProof ← mkKernelHomEqProof eqProofType rhs lhs maxLvl op_data
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

/-- The `kernel_hom` tactic transforms a kernel equality to an equivalent equality in
the category of measurable spaces and s-finite kernels.

The tactic supports location specifiers like `rw` or `simp`:
- `kernel_hom` — applies to the goal
- `kernel_hom at h` — applies to hypothesis `h`
- `kernel_hom at h₁ h₂` — applies to multiple hypotheses
- `kernel_hom at h ⊢` — applies to hypothesis `h` and the goal
- `kernel_hom at *` — applies to all hypotheses and the goal

Example:
```lean
example {W X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    [MeasurableSpace W] (κ : Kernel X Y) (η : Kernel Y Z) (ξ : Kernel Z W)
    [IsFiniteKernel ξ] [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    ξ ∘ₖ (η ∘ₖ κ) = ξ ∘ₖ η ∘ₖ κ := by
  kernel_hom
  exact Category.assoc _ _ _
``` -/
syntax "kernel_hom" (ppSpace location)? : tactic

elab_rules : tactic
  | `(tactic| kernel_hom $[$loc]?) =>
    expandOptLocation (Lean.mkOptionalNode loc) |> applyLocTactic <| applyKernelHom
