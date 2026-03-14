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
import LeanStoch.Tactic.Universe

open Lean Elab Tactic Meta CategoryTheory Parser.Tactic ProbabilityTheory Kernel MonoidalCategory

def get_types_from_kernel (κ : Expr) : MetaM ((Expr × Expr) × (Level × Level)) := do
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
    return ((X, Y), (xLevel, yLevel))
  | _ => throwError "Expected a kernel type, got: {κType}"

partial def construct_measurable_equiv (X : Expr) (xLevel maxLvl : Level) : MetaM Expr := do
  let Xwhnf ← whnf X
  match Xwhnf.getAppFn with
  | Expr.const ``PUnit _ =>
    mkAppOptM' (Expr.const `MeasurableEquiv.punit [maxLvl, xLevel]) #[]
  | Expr.const ``Prod univs =>
    let args := Xwhnf.getAppArgs
    let X := args[0]!
    let Y := args[1]!
    let xLevel := univs[0]!
    let yLevel := univs[1]!
    let ex ← construct_measurable_equiv X xLevel maxLvl
    let ey ← construct_measurable_equiv Y yLevel maxLvl
    mkAppOptM' (Expr.const `MeasurableEquiv.prod [maxLvl, xLevel, yLevel])
      #[none, none, none, none, none, none, none, none, ex, ey]
  | _ => mkAppOptM' (Expr.const `MeasurableEquiv.ulift [xLevel, maxLvl]) #[X, none]

def check_leftUnitor (κ : Expr) : MetaM Bool := do
  let κ := κ.consumeMData
  if !κ.getAppFn.isConstOf ``ProbabilityTheory.Kernel.map then
    return false
  let args := κ.getAppArgs
  let fn := args[args.size - 1]!
  let idKernel := args[args.size - 2]!
  if !fn.getAppFn.isConstOf ``Prod.snd then
    return false
  if !idKernel.getAppFn.isConstOf ``ProbabilityTheory.Kernel.id then
    return false
  let ((src, _), _) ← get_types_from_kernel κ
  let srcWhnf ← whnf src
  match srcWhnf.getAppFn with
  | Expr.const ``Prod _ =>
    let args := srcWhnf.getAppArgs
    if args.size < 2 then
      return false
    let left := args[0]!
    match left.getAppFn with
    | Expr.const ``PUnit _ => return true
    | _ => return false
  | _ => return false

abbrev LvlExpr := Level × Expr

/-- Transform a kernel expression to its quiver representation with explicit universe level for w.
- Replace `κ₁ ∘ₖ κ₂` (`Kernel.comp`) with `quiver κ₂ ≫ quiver κ₁`
- Replace `κ ⊗≫ₖ η` (`Kernel.monoComp`) with `quiver κ ⊗≫ quiver η`
- Replace single kernels with `quiver κ` -/
partial def transformKernelToQuiver (maxLvl : Level) (e : Expr) (left_equivs : List LvlExpr) :
    MetaM (Expr × List LvlExpr) := do
  match e.getAppFn with
  | Expr.const `ProbabilityTheory.Kernel.comp _ =>
    let args := e.getAppArgs
    if args.size >= 2 then
      let κ := args[args.size - 2]!
      let η := args[args.size - 1]!
      -- Recursively transform both kernels
      let (κ', lκ) ← transformKernelToQuiver maxLvl κ left_equivs
      let (η', lη) ← transformKernelToQuiver maxLvl η lκ
      -- Create categorical composition: η' ≫ κ' (reversed order)
      return (← mkAppM `CategoryTheory.CategoryStruct.comp #[η', κ'], lη)
    else
      throwError "Kernel.comp with insufficient arguments"
  | Expr.const `ProbabilityTheory.Kernel.monoComp _ =>
    let args := e.getAppArgs
    if args.size >= 2 then
      let κ := args[args.size - 4]!
      let η := args[args.size - 2]!
      let ((_, X), (_, xLevel)) ← get_types_from_kernel κ
      let ((Y, _), (yLevel, _)) ← get_types_from_kernel η
      let (κ', lκ) ← transformKernelToQuiver maxLvl κ left_equivs
      let (η', lη) ← transformKernelToQuiver maxLvl η lκ
      -- Create monoidal composition: quiver κ ⊗≫ quiver η
      let ex ← construct_measurable_equiv X xLevel maxLvl
      let ey ← construct_measurable_equiv Y yLevel maxLvl
      let monoComp := Expr.const `CategoryTheory.monoidalComp [maxLvl, maxLvl.succ]
      let monoCoherenceConst := Expr.const `MeasurableCoherence.monoidalCoherence
        [maxLvl, xLevel, yLevel]
      let monoCoherence ← mkAppOptM' monoCoherenceConst
        #[none, none, none, none, none, none, none, none, none, ex, ey]
      return (← mkAppOptM' monoComp
        #[none, none, none, none, none, none, monoCoherence, κ', η'], lη)
    else
         throwError "Kernel.monoComp with insufficient arguments"
  | _ =>
    let ((X, Y), (xLevel, yLevel)) ← get_types_from_kernel e
    if ← check_leftUnitor e then
      let punit_level ← match (← whnf X).getAppFn with
        | Expr.const ``Prod univs =>
          pure univs[0]!
        | _ => throwError "Expected left unitor with source PUnit × X, got: {X}"
      let stochOf ←
        match ← whnf Y with
        | Expr.const ``PUnit _ =>
          let stoch := Expr.const `Stoch [maxLvl]
          let tensorunit :=
            Expr.const `CategoryTheory.MonoidalCategoryStruct.tensorUnit [maxLvl, maxLvl.succ]
          mkAppOptM' tensorunit #[stoch, none, none]
        | _ =>
          let target ← mkAppM' (Expr.const `ULift [maxLvl, yLevel]) #[Y]
          let stochOfconst := Expr.const `Stoch.of [maxLvl]
          mkAppOptM' stochOfconst #[target, none]
      let leftunitor ← mkAppM `CategoryTheory.MonoidalCategoryStruct.leftUnitor #[stochOf]
      let ey ← construct_measurable_equiv Y yLevel maxLvl
      return (← mkAppM `CategoryTheory.Iso.hom #[leftunitor], left_equivs ++ [(punit_level, ey)])
    else
      -- Single kernel, transform to quiver.{maxLvl} ex ey κ
      let quiverConst := Expr.const `ProbabilityTheory.Kernel.quiver [maxLvl, xLevel, yLevel]
      let ex ← construct_measurable_equiv X xLevel maxLvl
      let ey ← construct_measurable_equiv Y yLevel maxLvl
      return( ← mkAppOptM' quiverConst
        #[none, none, none, none, none, none, none, none, ex, ey, e, none], left_equivs)

/-- Transform both sides of an equality by converting kernels to quivers. -/
def transformEquality (maxLvl : Level) (e : Expr) : MetaM (Expr × List LvlExpr) := do
  if e.isAppOfArity `Eq 3 then
    let (lhs, lh) ← transformKernelToQuiver maxLvl e.getAppArgs[1]! []
    let (rhs, rh) ← transformKernelToQuiver maxLvl e.getAppArgs[2]! lh
    return (← mkAppM `Eq #[lhs, rhs], rh)
  else
    throwError "Expected an equality, got: {e}"

def mkKernelQuiverEqProof (eqProofType : Expr) (maxLvl : Level) (left_equivs : List LvlExpr) :
    TacticM Expr := do
  let maxLevelStx ← liftMacroM <| levelToSyntax maxLvl
  let savedGoals ← getGoals
  let mvar ← mkFreshExprSyntheticOpaqueMVar eqProofType
  let mvarId := mvar.mvarId!
  setGoals [mvarId]

  evalTactic (← `(tactic| apply propext))
  evalTactic (← `(tactic| constructor))
  let goalsAfterConstructor ← getGoals
  match goalsAfterConstructor with
  | [forwardGoal, backwardGoal] =>
    -- Modus ponens direct. Try to use congruence on kernel compositions.
    setGoals [forwardGoal]
    evalTactic (← `(tactic| intro h))
    evalTactic (← `(tactic|
      try simp only [
        quiver_monoComp.{$maxLevelStx},
        quiver_comp.{$maxLevelStx},
        quiver_congr.{$maxLevelStx},
      ]
    ))
    evalTactic (← `(tactic|
      try simp only [
        quiver_comp.{$maxLevelStx},
        quiver_congr.{$maxLevelStx}
      ]
    ))

    -- Unfold `tensorUnit` if it appears, then try to rewrite unitors.
    evalTactic (← `(tactic| try dsimp only [MonoidalCategoryStruct.tensorUnit]))
    for e in left_equivs do
      let eStx ← Term.exprToSyntax e.2
      let punitLevelStx ← liftMacroM <| levelToSyntax e.1
      evalTactic (← `(tactic| try rw [Kernel.leftUnitor.{$maxLevelStx, _, $punitLevelStx}
        (ex := $eStx)]))

    -- Try to use congruence lemmas to close the goal, then try to solve with assumptions.
    evalTactic (← `(tactic| try simp only [quiver_congr.{$maxLevelStx}]))
    evalTactic (← `(tactic| assumption))

    -- Modus ponens reverse
    setGoals [backwardGoal]
    evalTactic (← `(tactic| intro h))
    evalTactic (← `(tactic|
      try simp only [
        quiver_monoComp.{$maxLevelStx},
        quiver_comp.{$maxLevelStx},
        quiver_congr.{$maxLevelStx},
      ] at h
    ))
    evalTactic (← `(tactic|
      try simp only [
        quiver_comp.{$maxLevelStx},
        quiver_congr.{$maxLevelStx}
      ] at h
    ))
    evalTactic (← `(tactic| try dsimp only [MonoidalCategoryStruct.tensorUnit] at h))
    for e in left_equivs do
      let eStx ← Term.exprToSyntax e.2
      let punitLevelStx ← liftMacroM <| levelToSyntax e.1
      evalTactic (← `(tactic| try rw [Kernel.leftUnitor.{$maxLevelStx, _, $punitLevelStx}
        (ex := $eStx)] at h))
    evalTactic (← `(tactic| try simp only [quiver_congr.{$maxLevelStx}] at h))
    evalTactic (← `(tactic| assumption))
  | _ =>
    setGoals savedGoals
    throwError "Expected exactly two goals after `constructor`"

  if !(← getGoals).isEmpty then
    setGoals savedGoals
    throwError "Failed to solve all goals while building kernel_quiver equivalence proof"

  setGoals savedGoals
  instantiateMVars mvar

def applyKernelQuiver (goal : MVarId) (fvarId : Option FVarId) : TacticM MVarId := do
  goal.withContext do
    let expr ← match fvarId with
        | some fid => do
          let decl ← fid.getDecl
          pure decl.type
        | none => goal.getType
    let allLevels ← collectKernelUniverses expr
    let uniqueLevels := allLevels.eraseDups
    -- Compute the maximum level
    let maxLvl ← match uniqueLevels with
      | [] => throwError "No universe levels found in the expression"
      | head :: tail => pure (tail.foldl Level.max head)
    let (quiverExpr, left_equivs) ← transformEquality maxLvl expr
    let eqProofType ← mkEq expr quiverExpr
    let eqProof ← mkKernelQuiverEqProof eqProofType maxLvl left_equivs
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

/-- The `kernel_quiver` tactic transforms a kernel equality to its quiver representation.

- Collects all universe levels from the equality
- Uses the maximum level for the `w` parameter in `quiver`
- Transforms both sides: kernels become `quiver κ`
- Rewrites compositions `κ₁ ∘ₖ κ₂` as `quiver κ₂ ≫ quiver κ₁`
- Rewrites monoidal compositions `κ ⊗≫ₖ η` as `quiver κ ⊗≫ quiver η`
- Detects `Kernel.leftUnitor` shapes coming from `Kernel.id.map Prod.snd` and rewrites
  the resulting quiver expression as the left unitor isomorphism.

The tactic supports location specifiers like `rw` or `simp`:
- `kernel_quiver` — applies to the goal
- `kernel_quiver at h` — applies to hypothesis `h`
- `kernel_quiver at h₁ h₂` — applies to multiple hypotheses
- `kernel_quiver at h ⊢` — applies to hypothesis `h` and the goal
- `kernel_quiver at *` — applies to all hypotheses and the goal

Example:
```lean
example {W X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    [MeasurableSpace W] (κ : Kernel X Y) (η : Kernel Y Z) (ξ : Kernel Z W)
    [IsFiniteKernel ξ] [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    ξ ∘ₖ (η ∘ₖ κ) = ξ ∘ₖ η ∘ₖ κ := by
  kernel_quiver
  exact Category.assoc _ _ _
``` -/
syntax "kernel_quiver" (ppSpace location)? : tactic

elab_rules : tactic
  | `(tactic| kernel_quiver $[$loc]?) => do
    expandOptLocation (Lean.mkOptionalNode loc) |> applyLocTactic <| applyKernelQuiver

example {W X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    [MeasurableSpace W] (κ : Kernel X Y) (η : Kernel Y Z) (ξ : Kernel Z W)
    (t : Kernel W X) [IsSFiniteKernel t]
    [IsFiniteKernel ξ] [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    t ∘ₖ ξ ∘ₖ (κ ⊗≫ₖ η) = t ∘ₖ (ξ ∘ₖ (κ ⊗≫ₖ η)) := by
  kernel_quiver
  simp only [Category.assoc]
