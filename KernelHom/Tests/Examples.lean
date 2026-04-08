/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import KernelHom.Tactic.Tactics
import Mathlib

open MeasureTheory ProbabilityTheory CategoryTheory BraidedCategory MonoidalCategory

open scoped ComonObj

variable {X Y Z T X' Y' Z' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace Z] [MeasurableSpace T] [MeasurableSpace X'] [MeasurableSpace Y']
  [MeasurableSpace Z']

namespace ProbabilityTheory.Kernel

variable {κ : Kernel X Y} {ξ : Kernel Z T} {η : Kernel Y Z}

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

variable [IsSFiniteKernel κ]

variable {κ' : Kernel X Y'} {η' : Kernel Y' Z'} [IsSFiniteKernel κ'] [IsSFiniteKernel η']

/-- `parallelComp_comp_parallelComp` -/
-- ANCHOR: parallelComp_comp_parallelComp
example : (η ∥ₖ η') ∘ₖ (κ ∥ₖ κ') = (η ∘ₖ κ) ∥ₖ (η' ∘ₖ κ') := by
  kernel_monoidal
-- ANCHOR_END: parallelComp_comp_parallelComp

/-- `parallelComp_comp_prod` -/
-- ANCHOR: parallelComp_comp_prod
example : (η ∥ₖ η') ∘ₖ (κ ×ₖ κ') = (η ∘ₖ κ) ×ₖ (η' ∘ₖ κ') := by
  kernel_monoidal
-- ANCHOR_END: parallelComp_comp_prod

/-- `deterministic_comp_copy` -/
-- ANCHOR: deterministic_comp_copy
example {f : X → Y} (hf : Measurable f) :
    (deterministic f hf ∥ₖ deterministic f hf) ∘ₖ copy X = copy Y ∘ₖ deterministic f hf := by
  kernel_hom
  exact (Deterministic.copy_natural _).symm
-- ANCHOR_END: deterministic_comp_copy

-- ANCHOR: discard_comp_deterministic
example {f : X → Y} (hf : Measurable f) :
    Kernel.discard Y ∘ₖ (deterministic f hf) = Kernel.discard X := by
  kernel_hom
  exact Deterministic.discard_natural _
-- ANCHOR_END: discard_comp_deterministic

/-- Dummy example for Verso referencing -/
-- ANCHOR: dummy_example
example (h : η = 0) : η = 0 := by
  kernel_hom
  hom_kernel
  exact h
-- ANCHOR_END: dummy_example

end ProbabilityTheory.Kernel
