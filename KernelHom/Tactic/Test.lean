/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
import KernelHom.Tactic.Reassoc
import KernelHom.Tactic.KernelCat
import EqLift.Tactic.Kernel.KernelLift

/-!
-/

open ProbabilityTheory CategoryTheory ProbabilityTheory.Kernel

section

variable {X : Type x} {Y : Type y} [MeasurableSpace X] [MeasurableSpace Y] (κ η : Kernel X Y) (h : κ = η)
  [IsSFiniteKernel κ] [IsSFiniteKernel η]

variable {Z T : Type*} [MeasurableSpace Z] [MeasurableSpace T] (ξ : Kernel Z T)
  [IsSFiniteKernel ξ]

@[reassoc]
lemma swap_parallelComp_diag : swap Y T ∘ₖ (κ ∥ₖ ξ) = ξ ∥ₖ κ ∘ₖ swap X Z := by
  kernel_disch

#check swap_parallelComp_diag_assoc

include h in
@[reassoc]
lemma test : κ = η := h

#check test_assoc


example (h : κ = η) : κ = η := by
  test_handler h
  exact h

end

section

variable {C : Type*} [Category C] {X Z : C} (f g : X ⟶ Z) (h : f = g)

include h in
@[reassoc]
lemma test2 : f = g := h

#check test2_assoc

end
