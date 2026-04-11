/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Lean.Elab.Tactic.Location

/-!
# Tactic location support

This module provides utilities for applying tactics to multiple goals and hypotheses
specified by location patterns, following the standard Lean syntax (like in `rw` or `simp`).

## Main declarations

- `applyLocTactic`: applies a tactic to goals and hypotheses at specified locations.
-/

open Lean Elab Tactic Meta

/-- Apply a given tactic to all goals and/or hypotheses specified by a `Location`. -/
def applyLocTactic (loc : Location) (tactic : MVarId → Option FVarId → TacticM MVarId) :
    TacticM Unit := do
  match loc with
  | Location.targets hyps target =>
    for hyp in hyps do
      let hFVarId ← getFVarId hyp
      let newGoal ← tactic (← getMainGoal) (some hFVarId)
      replaceMainGoal [newGoal]
    if target then
      let newGoal ← tactic (← getMainGoal) none
      replaceMainGoal [newGoal]
  | Location.wildcard =>
    let goal ← getMainGoal
    goal.withContext do
      let lctx ← getLCtx
      let mut currentGoal := goal
      for decl in lctx do
        if decl.isImplementationDetail then continue
        try
          currentGoal ← tactic currentGoal (some decl.fvarId)
          replaceMainGoal [currentGoal]
        catch _ => continue
      try
        currentGoal ← tactic currentGoal none
        replaceMainGoal [currentGoal]
      catch _ => pure ()
