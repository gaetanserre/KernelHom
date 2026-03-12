/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Lean.Elab.Tactic.Location
import LeanStoch.MonoidalComp.Kernel
import LeanStoch.MonoidalComp.MeasurableCoherence
import LeanStoch.Tactic.LocTactic

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
      | [] => throwError "No universe levels found in the equality"
      | head :: tail => pure (tail.foldl Level.max head)
    let maxLevelStx ← liftMacroM <| levelToSyntax maxLvl
    -- Apply transformations
    match fvarId with
    | some fid => do
      let hName := (← fid.getDecl).userName
      withMainContext do
        evalTactic (← `(tactic| first
          | simp only [toQuiver_congr.{$maxLevelStx},
            toQuiver_comp.{$maxLevelStx},
            toQuiver_monoComp.{$maxLevelStx}]
            at $(mkIdent hName):ident
          | simp only [toQuiver_congr.{$maxLevelStx},
            toQuiver_comp.{$maxLevelStx}] at $(mkIdent hName):ident
        ))
        getMainGoal
    | none => do
      withMainContext do
        evalTactic (← `(tactic| first
          | simp only [toQuiver_congr.{$maxLevelStx},
            toQuiver_comp.{$maxLevelStx},
            toQuiver_monoComp.{$maxLevelStx}]
          | simp only [toQuiver_congr.{$maxLevelStx},
            toQuiver_comp.{$maxLevelStx}]
        ))
        getMainGoal

def applyQuiverKernel (goal : MVarId) (fvarId : Option FVarId) : TacticM MVarId := do
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
      | [] => throwError "No universe levels found in the equality"
      | head :: tail => pure (tail.foldl Level.max head)
    let maxLevelStx ← liftMacroM <| levelToSyntax maxLvl
    -- Apply transformations
    match fvarId with
    | some fid => do
      let hName := (← fid.getDecl).userName
      withMainContext do
        evalTactic (← `(tactic| first
          | simp only [← toQuiver_congr.{$maxLevelStx},
            ← toQuiver_comp.{$maxLevelStx},
            ← toQuiver_monoComp.{$maxLevelStx}]
            at $(mkIdent hName):ident
          | simp only [← toQuiver_congr.{$maxLevelStx},
            ← toQuiver_comp.{$maxLevelStx}] at $(mkIdent hName):ident
        ))
        getMainGoal
    | none => do
      withMainContext do
        evalTactic (← `(tactic| first
          | simp only [← toQuiver_congr.{$maxLevelStx},
            ← toQuiver_comp.{$maxLevelStx},
            ← toQuiver_monoComp.{$maxLevelStx}]
          | simp only [← toQuiver_congr.{$maxLevelStx},
            ← toQuiver_comp.{$maxLevelStx}]
        ))
        getMainGoal

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

syntax "quiver_kernel" (ppSpace location)? : tactic

elab_rules : tactic
  | `(tactic| quiver_kernel $[$loc]?) => do
    expandOptLocation (Lean.mkOptionalNode loc) |> applyLocTactic <| applyQuiverKernel

example {W X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    [MeasurableSpace W] (κ : Kernel X Y) (η : Kernel Y Z) (ξ : Kernel Z W)
    [IsFiniteKernel ξ] [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    ξ ∘ₖ (η ∘ₖ κ) = ξ ∘ₖ η ∘ₖ κ := by
  kernel_quiver
  exact Category.assoc _ _ _
