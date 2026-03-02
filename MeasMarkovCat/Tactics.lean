import Lean
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.Probability.Kernel.Composition.MapComap

open Lean Meta Elab Tactic CategoryTheory MeasureTheory ProbabilityTheory

/-- Tactic to find an instance of `IsMarkovKernel`. -/
elab "kernel_markov" : tactic => withMainContext do
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
      let lctx ← getLCtx
      for decl in lctx do
        if decl.isImplementationDetail then continue
        let declType ← instantiateMVars decl.type
        -- Check if the type is of the form `Measurable _`
        if declType.isAppOf ``Measurable then
          let declName := decl.userName
          evalTactic (← `(tactic| try exact Kernel.IsMarkovKernel.map _ $(mkIdent declName)))
          try
            let _ ← getMainGoal
          catch _ =>
            return ()
      throwError "kernel_markov tactic failed."

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
