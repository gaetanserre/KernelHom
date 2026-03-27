/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

module

public import Mathlib.Probability.Kernel.Composition.KernelLemmas

/-!
# Auxiliary lemmas for probability kernels

This file provides supporting lemmas about parallel composition, mapping, and composition
of probability kernels that are used in the definition of **SFinKer** as a Markov category.

## Main results

* `parallelComp_id_id`: Parallel composition of two identity kernels is the identity
* `comp_id_parallelComp`, `comp_parallelComp_id`: Simplification lemmas for kernel compositions
-/

@[expose] public section

open ProbabilityTheory MeasureTheory

namespace ProbabilityTheory.Kernel

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

@[simp]
lemma id_parallelComp_id :
    Kernel.id ∥ₖ Kernel.id = (Kernel.id : Kernel (X × Y) (X × Y)) := by
  ext : 1
  simp [parallelComp_apply, id_apply, Measure.dirac_prod_dirac]

lemma id_parallelComp_comp_parallelComp_id {Z γ : Type*} [MeasurableSpace Z]
    [MeasurableSpace γ] (κ₁ : Kernel X Y)
    (κ₂ : Kernel Z γ) [IsSFiniteKernel κ₁] [IsSFiniteKernel κ₂] :
    Kernel.id ∥ₖ κ₁ ∘ₖ (κ₂ ∥ₖ Kernel.id) = κ₂ ∥ₖ κ₁ := by
  rw [parallelComp_id_left_comp_parallelComp]
  congr
  exact comp_id κ₁

end ProbabilityTheory.Kernel
