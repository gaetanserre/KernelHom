import Lean
import Mathlib.CategoryTheory.Monoidal.Category

open Lean Meta Elab Tactic CategoryTheory

/-- Tactic to find an instance of `IsSFiniteKernel`.
First tries `infer_instance`. If that fails, it adds hypotheses `IsSFiniteKernel κ.1`
for all kernels `κ` of type `{ κ : Kernel X Y // IsSFiniteKernel k }` in the context,
then retries `infer_instance`. -/
elab "kernel_sfiniteness" : tactic => withMainContext do
    -- First, try to synthesize the instance directly
    let goal ← getMainGoal
    let goalType ← goal.getType
    let result ← observing? do
      synthInstance goalType
    match result with
    | some inst =>
      goal.assign inst
    | none =>
      -- Get the local context
      let lctx ← getLCtx
      -- For each local declaration, check if it's a subtype
      for decl in lctx do
        if decl.isImplementationDetail then continue
        let declType ← instantiateMVars decl.type
        if declType.isAppOf ``Subtype then
          -- Add `have := decl.2` to extract the IsSFiniteKernel proof
          let declName := decl.userName
          try
            evalTactic (← `(tactic| have := $(mkIdent declName).2))
          catch _ =>
            continue
      -- Retry infer_instance
      evalTactic (← `(tactic| infer_instance))

/-- Tactic to reduce goals about categorical equalities of kernels to a simpler form. -/
elab "cat_kernel" : tactic => do
  try
    evalTactic (← `(tactic| refine Subtype.ext ?_))
    evalTactic (← `(tactic| simp only))
  catch _ =>
    throwError "cat_kernel tactic failed: could not apply Subtype.ext"
  try
    evalTactic (← `(tactic| dsimp only [CategoryStruct.id, CategoryStruct.comp,
      MonoidalCategory.whiskerLeft, MonoidalCategory.whiskerRight,
      MonoidalCategory.tensorHom]))
  catch _ =>
    throwError "cat_kernel tactic failed: dsimp made no progress"
