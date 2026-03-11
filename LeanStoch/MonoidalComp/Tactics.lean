/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Mathlib
import LeanStoch.MonoidalComp.Kernel

open Lean Elab Tactic Meta CategoryTheory

namespace ProbabilityTheory.Kernel

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
  | Expr.const ``ProbabilityTheory.Kernel univs =>
    -- univs contains the universe levels for this kernel
    levels := univs
  | _ => pure ()
  match e with
  | Expr.app f a => do
    let levelsF ← collectKernelUniverses f
    let levelsA ← collectKernelUniverses a
    return levels ++ levelsF ++ levelsA
  | _ => return levels

/-- Transform a kernel expression to its quiver representation with explicit universe level for w.
- Replace `κ₁ ∘ₖ κ₂` (Kernel.comp) with `toQuiver κ₂ ≫ toQuiver κ₁`
- Replace single kernels with `toQuiver κ` -/
partial def transformKernelToQuiver (maxLvl : Level) (e : Expr) : MetaM Expr := do
  -- Check if this is a Kernel.comp application
  if e.isAppOf `ProbabilityTheory.Kernel.comp then
    let args := e.getAppArgs
    if args.size >= 2 then
      let κ := args[args.size - 2]!
      let η := args[args.size - 1]!
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
        let xLevel := _univs[0]!
        let yLevel := _univs[1]!
        -- Construct: toQuiver.{w, x, y}
        let toQuiverConst := Expr.const `ProbabilityTheory.Kernel.toQuiver [maxLvl, xLevel, yLevel]
        return ← mkAppOptM' toQuiverConst #[none, none, none, none, e, none]
    | _ =>
      -- Not a kernel, keep as is
      return e

/-- Transform both sides of an equality by converting kernels to quivers. -/
def transformEquality (maxLvl : Level) (e : Expr) : MetaM Expr := do
  if e.isAppOfArity `Eq 3 then
    let args := e.getAppArgs
    let lhs := args[1]!
    let rhs := args[2]!
    let lhs' ← transformKernelToQuiver maxLvl lhs
    let rhs' ← transformKernelToQuiver maxLvl rhs
    mkAppM `Eq #[lhs', rhs']
  else
    throwError "Expected an equality, got: {e}"

/-- Build a proof that transforms a kernel equality to a quiver morphism equality.
Uses `toQuiver_comp_iff` and `toQuiver_eq_iff` to build the proof. -/
def buildQuiverProof (hName : Name) (maxLvl : Level) (newType : Expr) : TacticM Expr := do
  -- Create a fresh metavariable for the goal
  let mvar ← mkFreshExprMVar newType
  let goal := mvar.mvarId!
  -- Save current goals
  let savedGoals ← getGoals
  setGoals [goal]
  let levelStx ← liftMacroM <| levelToSyntax maxLvl
  evalTactic (← `(tactic| rw [toQuiver_congr.{$levelStx}] at $(mkIdent hName):ident))
  evalTactic (← `(tactic| simpa [toQuiver_comp.{$levelStx}] using $(mkIdent hName)))
  let proof ← instantiateMVars mvar
  setGoals savedGoals
  return proof

/-- The `kernel_quiver` tactic transforms a kernel equality to its quiver representation.

- Collects all universe levels from the equality
- Uses the maximum level for the `w` parameter in `toQuiver`
- Transforms both sides: kernels become `toQuiver κ`, compositions `κ₁ ∘ₖ κ₂` become
`toQuiver κ₂ ≫ toQuiver κ₁`

Example:
```lean
example (κ : Kernel X Y) (η : Kernel Y Z) [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (h : η ∘ₖ κ = 0) : ... := by
  kernel_quiver at h
  -- Now h is: toQuiver η ≫ toQuiver κ = toQuiver 0
  ...
``` -/
syntax "kernel_quiver" "at" ident : tactic

elab_rules : tactic
  | `(tactic| kernel_quiver at $h:ident) => do
    let hName := h.getId
    let hFVarId ← getFVarId h
    let hDecl ← hFVarId.getDecl
    let hType := hDecl.type
    -- Check if this is an equality
    if hType.isAppOfArity `Eq 3 then
      logInfo m!"Analyzing equality: {hName}"
      let args := hType.getAppArgs
      let lhs := args[1]!
      let rhs := args[2]!
      -- Collect universes from both sides
      let levelsLhs ← collectKernelUniverses lhs
      let levelsRhs ← collectKernelUniverses rhs
      let allLevels := levelsLhs ++ levelsRhs
      let uniqueLevels := allLevels.eraseDups
      logInfo m!"\n=== All universe levels found ==="
      logInfo m!"Universe levels: {uniqueLevels}"
      -- Compute the maximum level
      let maxLvl ← match uniqueLevels with
        | [] => throwError "No universe levels found in the equality"
        | head :: tail => pure (tail.foldl Level.max head)
      logInfo m!"Maximum level: {maxLvl}"
      -- Transform the equality
      let newType ← transformEquality maxLvl hType
      logInfo m!"Transformed type: {newType}"
      -- Build a proof of `newType` using the kernel quiver lemmas
      let proof ← buildQuiverProof hName maxLvl newType
      -- Replace the original hypothesis with the new one
      let mvarId ← getMainGoal
      let res ← mvarId.replace hFVarId proof
      replaceMainGoal [res.mvarId]
    else
      throwError "Expected an equality, got: {hType}"

universe w x y z

variable {W X Y Z : Type*}
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace W]

example (κ : Kernel X Y) (η : Kernel Y Z) (ξ : Kernel Z W) (res : Kernel X W)
    [IsFiniteKernel ξ] [IsSFiniteKernel κ] [IsSFiniteKernel η] [IsSFiniteKernel res]
    (h : ξ ∘ₖ (η ∘ₖ κ) = res) : False := by
  kernel_quiver at h
  sorry

end ProbabilityTheory.Kernel
