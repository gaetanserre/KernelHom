/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Lean
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# Tactics for kernel automation

This file defines custom tactics for working with s-finite kernels in the category **Stoch**.

## Main definitions

* `kernel_sfinite`: automatically solves goals of the form `IsSFiniteKernel k` by searching for
  instances in the context
* `cat_kernel`: reduces categorical equality goals between kernels to simpler kernel equalities
  by unfolding categorical structure
-/

open Lean Meta Elab Tactic CategoryTheory MeasureTheory ProbabilityTheory

/-- Tactic to find an instance of `IsSFiniteKernel`. -/
elab "kernel_sfinite" : tactic => withMainContext do
    -- First, try to synthesize the instance directly
    evalTactic (← `(tactic| try dsimp only [MonoidalCategory.tensorUnit,
      MonoidalCategory.tensorObj]))
    let goal ← getMainGoal
    let goalType ← goal.getType
    -- First, try to find the instance directly
    let result ← synthInstance? goalType
    match result with
    | some inst =>
      goal.assign inst
    | none =>
      /- Explicitly add any `Subtype.prop` hypotheses to the context and try
      to infer the instance again -/
      let lctx ← getLCtx
      for decl in lctx do
        if decl.isImplementationDetail then continue
        let declName := decl.userName
        evalTactic (← `(tactic| try have := $(mkIdent declName).2))
      -- Retry infer_instance
      evalTactic (← `(tactic| try infer_instance))
      try
        let _ ← getMainGoal
      catch _ =>
        return ()
      throwError "kernel_sfinite tactic failed."

/-- Tactic to reduce goals about categorical equalities of kernels to a simpler form. -/
elab "cat_kernel" : tactic => do
  evalTactic (← `(tactic| try refine Subtype.ext ?_))
  evalTactic (← `(tactic| try simp only))
  try
    evalTactic (← `(tactic| dsimp only [CategoryStruct.id, CategoryStruct.comp,
      MonoidalCategory.whiskerLeft, MonoidalCategory.whiskerRight,
      MonoidalCategory.tensorHom, MonoidalCategory.tensorUnit, MonoidalCategory.tensorObj,
      MonoidalCategory.associator, MonoidalCategory.leftUnitor, MonoidalCategory.rightUnitor]))
  catch _ =>
    throwError "cat_kernel tactic failed: dsimp made no progress"
