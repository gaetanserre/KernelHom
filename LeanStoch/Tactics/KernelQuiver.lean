/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Lean.Elab.Tactic.Location
import LeanStoch.MonoidalComp.Kernel

open Lean Elab Tactic Meta CategoryTheory Parser.Tactic ProbabilityTheory Kernel

/-- Convert a Level to Syntax for use in tactic quotations. -/
partial def levelToSyntax (lvl : Level) : MacroM (TSyntax `level) := do
  match lvl with
  | Level.zero => `(level| 0)
  | Level.succ l => do
    let lStx : TSyntax `level ← levelToSyntax l
    `(level| $lStx + 1)
  | Level.param n => `(level| $(mkIdent n):ident)
  | Level.mvar _ => Macro.throwError "Cannot convert mvar level to syntax"
  | Level.max l1 l2 => do
    let l1Stx : TSyntax `level ← levelToSyntax l1
    let l2Stx : TSyntax `level ← levelToSyntax l2
    `(level| max $l1Stx $l2Stx)
  | Level.imax l1 l2 => do
    let l1Stx : TSyntax `level ← levelToSyntax l1
    let l2Stx : TSyntax `level ← levelToSyntax l2
    `(level| imax $l1Stx $l2Stx)

/-- Recursively traverse an expression and collect universe levels from all kernels found.
Returns a list of all universe levels encountered. -/
partial def collectKernelUniverses (e : Expr) : MetaM (List Level) := do
  -- Check if this is a kernel type
  let eType ← inferType e
  let mut levels : List Level := []
  match eType.getAppFn with
  | Expr.const ``Kernel univs =>
    -- univs contains the universe levels for this kernel
    levels := univs
  | _ => pure ()
  match e with
  | Expr.app f a => do
    let levelsF ← collectKernelUniverses f
    let levelsA ← collectKernelUniverses a
    return levels ++ levelsF ++ levelsA
  | _ => return levels

/-- Apply kernel_quiver transformation to a specific hypothesis or goal. -/
def applyKernelQuiver (goal : MVarId) (fvarId : Option FVarId) : TacticM MVarId := do
  goal.withContext do
    let eq ← match fvarId with
      | some fid => do
        let decl ← fid.getDecl
        pure decl.type
      | none => goal.getType
    if eq.isAppOfArity `Eq 3 then
      let args := eq.getAppArgs
      let lhs := args[1]!
      let rhs := args[2]!
      -- Collect universes from both sides
      let levelsLhs ← collectKernelUniverses lhs
      let levelsRhs ← collectKernelUniverses rhs
      let allLevels := levelsLhs ++ levelsRhs
      let uniqueLevels := allLevels.eraseDups
      -- Compute the maximum level
      let maxLvl ← match uniqueLevels with
        | [] => throwError "No universe levels found in the equality"
        | head :: tail => pure (tail.foldl Level.max head)
      let maxLevelStx ← liftMacroM <| levelToSyntax maxLvl
      -- Apply transformations
      match fvarId with
      | some fid => do
        let hName := (← fid.getDecl).userName
        withMainContext do
          evalTactic (← `(tactic| rw [toQuiver_congr.{$maxLevelStx}] at $(mkIdent hName):ident))
          evalTactic (← `(tactic|
            simp only [toQuiver_comp.{$maxLevelStx}] at $(mkIdent hName):ident))
          getMainGoal
      | none => do
        withMainContext do
          evalTactic (← `(tactic| rw [toQuiver_congr.{$maxLevelStx}]))
          evalTactic (← `(tactic| simp only [toQuiver_comp.{$maxLevelStx}]))
          getMainGoal
    else
      throwError "Expected an equality, got: {eq}"
    -- Check if this is an equality


/-- The `kernel_quiver` tactic transforms a kernel equality to its quiver representation.

- Collects all universe levels from the equality
- Uses the maximum level for the `w` parameter in `toQuiver`
- Transforms both sides: kernels become `toQuiver κ`, compositions `κ₁ ∘ₖ κ₂` become
`toQuiver κ₂ ≫ toQuiver κ₁`

The tactic supports location specifiers like `rw` or `simp`:
- `kernel_quiver` — applies to the goal
- `kernel_quiver at h` — applies to hypothesis `h`
- `kernel_quiver at h₁ h₂` — applies to multiple hypotheses
- `kernel_quiver at h ⊢` — applies to hypothesis `h` and the goal
- `kernel_quiver at *` — applies to all hypotheses and the goal

Example:
```lean
example (κ : Kernel X Y) (η : Kernel Y Z) [IsSFiniteKernel κ] [IsSFiniteKernel η] : η ∘ₖ κ = 0 := by
  kernel_quiver
  -- Now the goal is: toQuiver κ ≫ toQuiver η = toQuiver 0
  sorry
``` -/
syntax "kernel_quiver" (ppSpace location)? : tactic

elab_rules : tactic
  | `(tactic| kernel_quiver $[$loc]?) => do
    let loc := expandOptLocation (Lean.mkOptionalNode loc)
    match loc with
    | Location.targets hyps target => do
      -- Process each hypothesis
      for hyp in hyps do
        let hFVarId ← getFVarId hyp
        let newGoal ← applyKernelQuiver (← getMainGoal) (some hFVarId)
        replaceMainGoal [newGoal]
      -- Process target if requested
      if target then
        let newGoal ← applyKernelQuiver (← getMainGoal) none
        replaceMainGoal [newGoal]
    | Location.wildcard => do
      -- Apply to all hypotheses and goal
      let goal ← getMainGoal
      goal.withContext do
        let lctx ← getLCtx
        let mut currentGoal := goal
        for decl in lctx do
          if decl.isImplementationDetail then continue
          try
            currentGoal ← applyKernelQuiver currentGoal (some decl.fvarId)
            replaceMainGoal [currentGoal]
          catch _ => continue
        -- Apply to goal
        try
          currentGoal ← applyKernelQuiver currentGoal none
          replaceMainGoal [currentGoal]
        catch _ => pure ()

/- variable {W X Y Z : Type*}
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace W]

example (κ : Kernel X Y) (η : Kernel Y Z) (ξ : Kernel Z W) (res : Kernel X W)
    [IsFiniteKernel ξ] [IsSFiniteKernel κ] [IsSFiniteKernel η] [IsSFiniteKernel res]
    (h : ξ ∘ₖ (η ∘ₖ κ) = res) : ξ ∘ₖ (η ∘ₖ κ) = res := by
  kernel_quiver
  sorry -/
