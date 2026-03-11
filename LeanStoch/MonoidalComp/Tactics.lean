/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Mathlib
import LeanStoch.MonoidalComp.Kernel

open Lean Elab Tactic Meta CategoryTheory

namespace ProbabilityTheory.Kernel

/--
Recursively traverse an expression and collect universe levels from all kernels found.
Returns a list of all universe levels encountered.
-/
partial def collectKernelUniverses (e : Expr) : MetaM (List Level) := do
  -- Don't use whnf to avoid loose bvar issues

  -- Check if this is a kernel type
  let eType ← inferType e

  let mut levels : List Level := []

  match eType.getAppFn with
  | Expr.const ``ProbabilityTheory.Kernel univs =>
    -- univs contains the universe levels for this kernel
    levels := univs
  | _ => pure ()

  -- Only recurse on applications, not on lambda/forall to avoid loose bvar
  match e with
  | Expr.app f a => do
    let levelsF ← collectKernelUniverses f
    let levelsA ← collectKernelUniverses a
    return levels ++ levelsF ++ levelsA
  | _ => return levels

/--
Transform a kernel expression to its quiver representation with explicit universe level for w.
- Replace `κ₁ ∘ₖ κ₂` (Kernel.comp) with `toQuiver κ₂ ≫ toQuiver κ₁`
- Replace single kernels with `toQuiver κ`
-/
partial def transformKernelToQuiver (maxLvl : Level) (e : Expr) : MetaM Expr := do
  -- Check if this is a Kernel.comp application
  if e.isAppOf `ProbabilityTheory.Kernel.comp then
    let args := e.getAppArgs

    if args.size >= 2 then
      let idx1 := args.size - 2  -- κ (first kernel)
      let idx2 := args.size - 1  -- η (second kernel)

      let κ := args[idx1]!
      let η := args[idx2]!

      -- Recursively transform both kernels
      let κ' ← transformKernelToQuiver maxLvl κ
      let η' ← transformKernelToQuiver maxLvl η

      -- Create categorical composition: η' ≫ κ' (reversed order)
      mkAppM `CategoryTheory.CategoryStruct.comp #[η', κ']
    else
      throwError "Kernel.comp with insufficient arguments"
  else
    -- Check if this is a kernel
    let eType ← inferType e

    match eType.getAppFn with
    | Expr.const ``ProbabilityTheory.Kernel _univs =>
      let args := eType.getAppArgs
      if args.size >= 2 then
        let X := args[0]!
        let Y := args[1]!

        let xType ← inferType X
        let yType ← inferType Y

        -- Extract universe levels from the types
        let xLevel := match xType with
          | Expr.sort (Level.succ u) => u
          | Expr.sort u => u
          | _ => Level.zero

        let yLevel := match yType with
          | Expr.sort (Level.succ u) => u
          | Expr.sort u => u
          | _ => Level.zero

        -- Construct: toQuiver.{w, x, y}
        let toQuiverConst := Expr.const `ProbabilityTheory.Kernel.toQuiver [maxLvl, xLevel, yLevel]

        -- Apply toQuiver to the kernel
        -- We need to provide: X, Y, [MeasurableSpace X], [MeasurableSpace Y], κ, [IsSFiniteKernel κ]
        -- Manually build the application with instances
        let msX ← synthInstance (← mkAppM ``MeasurableSpace #[X])
        let msY ← synthInstance (← mkAppM ``MeasurableSpace #[Y])
        let sfinite ← synthInstance (← mkAppM ``ProbabilityTheory.IsSFiniteKernel #[e])

        return mkApp6 toQuiverConst X Y msX msY e sfinite
      else
        throwError "Insufficient arguments in kernel type: {eType}"
    | _ =>
      -- Not a kernel, keep as is
      return e

/--
Transform both sides of an equality by converting kernels to quivers.
-/
def transformEquality (maxLvl : Level) (e : Expr) : MetaM Expr := do
  if e.isAppOfArity `Eq 3 then
    let args := e.getAppArgs
    let lhs := args[1]!
    let rhs := args[2]!

    -- Transform both sides
    let lhs' ← transformKernelToQuiver maxLvl lhs
    let rhs' ← transformKernelToQuiver maxLvl rhs

    -- Reconstruct the equality
    mkAppM `Eq #[lhs', rhs']
  else
    throwError "Expected an equality, got: {e}"

/--
Build a proof that transforms a kernel equality to a quiver morphism equality.
Uses toQuiver_comp_iff and toQuiver_eq_iff to build the proof.
-/
def buildQuiverProof (hName : Name) (hFVar : Expr) (hExpr : Expr) (maxLvl : Level) (newType : Expr) : TacticM Expr := do
  -- Create a fresh metavariable for the goal
  let mvar ← mkFreshExprMVar newType
  let goal := mvar.mvarId!

  -- Save current goals
  let savedGoals ← getGoals
  setGoals [goal]

  let args := hExpr.getAppArgs
  let lhs := args[1]!
  let rhs := args[2]!
  let lhsType ← inferType lhs

  match lhsType.getAppFn with
    | Expr.const ``ProbabilityTheory.Kernel _univs =>
      let args := lhsType.getAppArgs
      if args.size >= 2 then
        let X := args[0]!
        let Y := args[1]!

        let xType ← inferType X
        let yType ← inferType Y

        -- Extract universe levels from the types
        let xLevel := match xType with
          | Expr.sort (Level.succ u) => u
          | Expr.sort u => u
          | _ => Level.zero

        let yLevel := match yType with
          | Expr.sort (Level.succ u) => u
          | Expr.sort u => u
          | _ => Level.zero

        -- Build toQuiver_congr.{maxLvl} explicitly
        let toQuiverCongrConst := Expr.const `ProbabilityTheory.Kernel.toQuiver_congr [maxLvl, xLevel, yLevel]

        -- Apply toQuiver_congr fully to get an Iff
        let iffExpr ← mkAppOptM' toQuiverCongrConst #[X, Y, none, none, lhs, rhs, none, none]

        -- Get Iff.mp to convert kernel equality to quiver equality
        let mpExpr ← mkAppM `Iff.mp #[iffExpr, hFVar]

        let res ← goal.note `h_quiver mpExpr

        setGoals [res.2]

        evalTactic (← `(tactic| repeat rw [toQuiver_comp] at $(mkIdent `h_quiver):ident))
        evalTactic (← `(tactic| assumption))

        let proof ← instantiateMVars mvar
        setGoals savedGoals
        return proof
      else
        throwError "Insufficient arguments in kernel type: {lhs}"
    | _ =>
      throwError "Expected a kernel equality, got: {lhs}"

/--
The `kernel_quiver` tactic transforms a kernel equality to its quiver representation.

- Collects all universe levels from the equality
- Uses the maximum level for the `w` parameter in `toQuiver`
- Transforms both sides: kernels become `toQuiver κ`, compositions `κ₁ ∘ₖ κ₂` become `toQuiver κ₂ ≫ toQuiver κ₁`

Example:
```lean
example (κ : Kernel X Y) (η : Kernel Y Z) [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (h : η ∘ₖ κ = 0) : ... := by
  kernel_quiver at h
  -- Now h is: toQuiver η ≫ toQuiver κ = toQuiver 0
  ...
```
-/
syntax "kernel_quiver" "at" ident : tactic

elab_rules : tactic
  | `(tactic| kernel_quiver at $h:ident) => do
    let hName := h.getId
    let hFVarId ← getFVarId h
    let hDecl ← hFVarId.getDecl
    let hType := hDecl.type

    logInfo m!"Analyzing equality: {hName}"

    -- Check if this is an equality
    if hType.isAppOfArity `Eq 3 then
      let args := hType.getAppArgs
      let lhs := args[1]!
      let rhs := args[2]!

      -- Collect universes from both sides
      let levelsLhs ← collectKernelUniverses lhs
      let levelsRhs ← collectKernelUniverses rhs

      let allLevels := levelsLhs ++ levelsRhs

      -- Remove duplicates
      let uniqueLevels := allLevels.eraseDups

      logInfo m!"\n=== All universe levels found ==="
      logInfo m!"Unique levels: {uniqueLevels}"

      -- Compute the maximum level
      let maxLvl ← match uniqueLevels with
        | [] => throwError "No universe levels found in the equality"
        | head :: tail => pure (tail.foldl Level.max head)

      logInfo m!"Maximum level for w: {maxLvl}"

      -- Transform the equality
      let newType ← transformEquality maxLvl hType
      logInfo m!"Transformed type: {newType}"

      -- Create a new hypothesis with the transformed type
      -- The original hypothesis h is kept
      let mvarId ← getMainGoal

      -- Build a proof using the kernel quiver lemmas
      let proof ← buildQuiverProof hName (mkFVar hFVarId) hType maxLvl newType

      -- Use note (shorthand for have with a proof) to add the new hypothesis
      --let (_, newMvarId) ← mvarId.note newHName proof
      let res ← mvarId.replace hFVarId proof
      --let newMvarId ← res.mvarId.clear fid

      replaceMainGoal [res.mvarId]
    else
      throwError "Expected an equality, got: {hType}"

universe w x y z

variable {W : Type w} {X : Type x} {Y : Type y} {Z : Type z}
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace W]

example (κ : Kernel X Y) (η : Kernel Y Z) (ξ : Kernel Z W) (res : Kernel X Z)
    [IsFiniteKernel ξ] [IsSFiniteKernel κ] [IsSFiniteKernel η] [IsSFiniteKernel res]
    (h : ξ ∘ₖ (η ∘ₖ κ) = 0) : False := by
  rw [toQuiver_congr] at h
  rw [toQuiver_comp] at h
  rw [toQuiver_comp] at h
  -- {max (max x y z) z, x}
  -- {max (max v x) y, w}
  --rw [toQuiver_comp] at h
  --rw [toQuiver_congr, toQuiver_comp] at h
  --have := toQuiver_comp_iff (κ₁ := η) (κ₂ := κ) (κ₃ := 0) (Z := X)
  --rw [toQuiver_comp_iff] at h
  /- simp [toQuiver_congr.{max w x y z}, toQuiver_comp] at h
  rw [toQuiver_congr.{max w x y z}] at h
  rw [toQuiver_comp] at h
  rw [toQuiver_comp] at h
  let t := toQuiver.{max x z w} (η ∘ₖ κ)
  --rw [toQuiver_comp (κ₁ := η) (κ₂ := κ)] at h
  --rw [toQuiver_comp] at h -/
  kernel_quiver at h
  -- Now we should have both h (original) and h_quiver (transformed) in context
  sorry

end ProbabilityTheory.Kernel
