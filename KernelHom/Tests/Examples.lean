/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import KernelHom.Tactic.Tactics

open MeasureTheory ProbabilityTheory CategoryTheory BraidedCategory MonoidalCategory

open scoped ComonObj

variable {W X Y Z T : Type*} [MeasurableSpace W] [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace Z] [MeasurableSpace T] {κ : Kernel X Y} {η : Kernel W Z} {ξ : Kernel Z T}

namespace ProbabilityTheory.Kernel

/-- `swap_parallelComp` -/
-- ANCHOR: swap_parallelComp
example : swap Y T ∘ₖ (κ ∥ₖ ξ) = ξ ∥ₖ κ ∘ₖ swap X Z := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  by_cases hη : IsSFiniteKernel ξ
  swap; · simp [hη]
  kernel_hom
  exact braiding_naturality _ _
-- ANCHOR_END: swap_parallelComp

variable [IsSFiniteKernel η] [IsSFiniteKernel ξ]

/-- `parallelComp_id_left_comp_parallelComp` -/
-- ANCHOR: parallelComp_id_left_comp_parallelComp
example : (Kernel.id ∥ₖ ξ) ∘ₖ (κ ∥ₖ η) = κ ∥ₖ (ξ ∘ₖ η) := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  kernel_monoidal
-- ANCHOR_END: parallelComp_id_left_comp_parallelComp

/-- `parallelComp_id_right_comp_parallelComp` -/
-- ANCHOR: parallelComp_id_right_comp_parallelComp
example : (ξ ∥ₖ Kernel.id) ∘ₖ (η ∥ₖ κ) = (ξ ∘ₖ η) ∥ₖ κ := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  kernel_monoidal
-- ANCHOR_END: parallelComp_id_right_comp_parallelComp

/-- Dummy example for Verso referencing -/
-- ANCHOR: dummy_example
example (h : η = 0) : η = 0 := by
  kernel_hom
  hom_kernel
  exact h
-- ANCHOR_END: dummy_example

end ProbabilityTheory.Kernel
