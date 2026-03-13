/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Lean.Elab.Tactic.Location
import LeanStoch.MonoidalComp.Kernel
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

def construct_measurable_equiv (X : Expr) (xLevel maxLvl : Level) : MetaM Expr := do
  let Xwhnf ← whnf X
  match Xwhnf.getAppFn with
  | Expr.const ``Prod univs =>
    let args := Xwhnf.getAppArgs
    let X := args[0]!
    let Y := args[1]!
    let xLevel := univs[0]!
    let yLevel := univs[1]!
    mkAppOptM' (Expr.const `MeasurableEquiv.ulift_prod [maxLvl, xLevel, yLevel]) #[X, Y, none, none]
  | _ => mkAppOptM' (Expr.const `MeasurableEquiv.ulift [xLevel, maxLvl]) #[X, none]

/-- Transform a kernel expression to its quiver representation with explicit universe level for w.
- Replace `κ₁ ∘ₖ κ₂` (`Kernel.comp`) with `quiver κ₂ ≫ quiver κ₁`
- Replace `κ ⊗≫ₖ η` (`Kernel.monoComp`) with `quiver κ ⊗≫ quiver η`
- Replace single kernels with `quiver κ` -/
partial def transformKernelToQuiver (maxLvl : Level) (e : Expr) : MetaM Expr := do
  -- Check if this is a Kernel.comp application
  match e.getAppFn with
  | Expr.const `ProbabilityTheory.Kernel.comp _ =>
    let args := e.getAppArgs
    if args.size >= 2 then
      let κ := args[args.size - 2]!
      let η := args[args.size - 1]!
      -- Recursively transform both kernels
      let κ' ← transformKernelToQuiver maxLvl κ
      let η' ← transformKernelToQuiver maxLvl η
      -- Create categorical composition: η' ≫ κ' (reversed order)
      return ← mkAppM `CategoryTheory.CategoryStruct.comp #[η', κ']
    else
      throwError "Kernel.comp with insufficient arguments"
  | Expr.const `ProbabilityTheory.Kernel.monoComp _ =>
    let args := e.getAppArgs
    if args.size >= 2 then
      let κ := args[args.size - 4]!
      let η := args[args.size - 2]!
      let ((_, X), (_, xLevel)) ← get_types_from_kernel κ
      let ((Y, _), (yLevel, _)) ← get_types_from_kernel η
      let κ' ← transformKernelToQuiver maxLvl κ
      let η' ← transformKernelToQuiver maxLvl η
        -- Create monoidal composition: quiver κ ⊗≫ quiver η
      let ex ← construct_measurable_equiv X xLevel maxLvl
      let ey ← construct_measurable_equiv Y yLevel maxLvl
      let monoComp := Expr.const `CategoryTheory.monoidalComp [maxLvl, maxLvl.succ]
      let monoCoherenceConst := Expr.const `MeasurableCoherence.monoidalCoherence
        [maxLvl, xLevel, yLevel]
      let monoCoherence ← mkAppOptM' monoCoherenceConst
        #[none, none, none, none, none, none, none, none, none, ex, ey]
      return ← mkAppOptM' monoComp
        #[none, none, none, none, none, none, monoCoherence, κ', η']
    else
         throwError "Kernel.monoComp with insufficient arguments"
  -- A single kernel, replace with quiver
  | _ =>
    let ((X, Y), (xLevel, yLevel)) ← get_types_from_kernel e
    -- Construct: quiver.{maxLvl} ex ey κ
    let quiverConst := Expr.const `ProbabilityTheory.Kernel.quiver [maxLvl, xLevel, yLevel]
    let ex ← construct_measurable_equiv X xLevel maxLvl
    let ey ← construct_measurable_equiv Y yLevel maxLvl
    let res ← mkAppOptM' quiverConst
      #[none, none, none, none, none, none, none, none, ex, ey, e, none]
    return res

/-- Transform both sides of an equality by converting kernels to quivers. -/
def transformEquality (maxLvl : Level) (e : Expr) : MetaM Expr := do
  if e.isAppOfArity `Eq 3 then
    let lhs ← transformKernelToQuiver maxLvl e.getAppArgs[1]!
    let rhs ← transformKernelToQuiver maxLvl e.getAppArgs[2]!
    return ← mkAppM `Eq #[lhs, rhs]
  else
    throwError "Expected an equality, got: {e}"

def mkKernelQuiverEqProof (eqProofType : Expr) (maxLvl : Level) : TacticM Expr := do
  let maxLevelStx ← liftMacroM <| levelToSyntax maxLvl
  let proofStx ← `(by
    apply propext
    constructor
    · intro h
      first
      | simpa only [
        ← quiver_monoComp.{$maxLevelStx},
        ← quiver_congr.{$maxLevelStx},
        ← quiver_comp.{$maxLevelStx}
       ]
      | simpa only [
        ← quiver_congr.{$maxLevelStx},
        ← quiver_comp.{$maxLevelStx}
       ]
    · intro h
      first
      | simpa only [
        ← quiver_congr.{$maxLevelStx},
        ← quiver_comp.{$maxLevelStx},
        ← quiver_monoComp.{$maxLevelStx}
       ] using h
      | simpa only [
        ← quiver_congr.{$maxLevelStx},
        ← quiver_comp.{$maxLevelStx}
       ] using h
  )
  Term.withSynthesize <| Term.elabTermEnsuringType proofStx eqProofType

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
    let quiverExpr ← transformEquality maxLvl expr
    let eqProofType ← mkEq expr quiverExpr
    let eqProof ← mkKernelQuiverEqProof eqProofType maxLvl
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
