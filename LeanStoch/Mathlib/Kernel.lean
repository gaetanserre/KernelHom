/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Mathlib.Probability.Kernel.Composition.KernelLemmas

/-!
# Auxiliary lemmas for probability kernels

This file provides supporting lemmas about parallel composition, mapping, and composition
of probability kernels that are used in the definition of **Stoch** as a Markov category.

## Main results

* `parallelComp_id_id`: Parallel composition of two identity kernels is the identity
* `comp_id_parallelComp`, `comp_parallelComp_id`: Simplification lemmas for kernel compositions
-/

open ProbabilityTheory MeasureTheory

namespace ProbabilityTheory.Kernel

/-- The Markov kernel to the `PUnit` type. -/
noncomputable
def Udiscard (α : Type*) [MeasurableSpace α] : Kernel α PUnit :=
  Kernel.deterministic (fun _ ↦ PUnit.unit) measurable_const

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

instance : IsMarkovKernel (Udiscard α) := by rw [Udiscard]; infer_instance

@[simp]
lemma parallelComp_id_id :
    Kernel.id ∥ₖ Kernel.id = (Kernel.id : Kernel (α × β) (α × β)) := by
  ext x s hs
  simp [parallelComp_apply, id_apply, Measure.dirac_prod_dirac]

@[simp]
lemma parallelComp_id_id_comp_parallelComp_id_id :
    (Kernel.id ∥ₖ Kernel.id) ∘ₖ (Kernel.id ∥ₖ Kernel.id)
      = (Kernel.id : Kernel (α × β) (α × β)) := by
  rw [parallelComp_id_id]
  simp only [comp_id]

lemma parallelComp_id_id_map {ι : Type*} [MeasurableSpace ι] {f : α → β} (hf : Measurable f) :
   Kernel.id ∥ₖ Kernel.id.map f =
    (Kernel.id.map (fun x => (x.1, f x.2)) : Kernel (ι × α) (ι × β)) := by
  rw [id_map hf, id_map (by fun_prop)]
  ext x s hs
  simp [parallelComp_apply, id_apply,
    deterministic_apply, Measure.dirac_prod_dirac]

lemma parallelComp_id_map_id {ι : Type*} [MeasurableSpace ι] {f : α → β} (hf : Measurable f) :
   Kernel.id.map f ∥ₖ Kernel.id =
    (Kernel.id.map (fun x => (f x.1, x.2)) : Kernel (α × ι) (β × ι)) := by
  rw [id_map hf, id_map (by fun_prop)]
  ext x s hs
  simp [parallelComp_apply, id_apply,
    deterministic_apply, Measure.dirac_prod_dirac]

@[simp]
lemma comp_id_parallelComp {ι γ : Type*} [MeasurableSpace ι] [MeasurableSpace γ] (κ₁ : Kernel α β)
    (κ₂ : Kernel ι γ) [IsSFiniteKernel κ₁] [IsSFiniteKernel κ₂] :
    Kernel.id ∥ₖ κ₁ ∘ₖ (κ₂ ∥ₖ Kernel.id) = κ₂ ∥ₖ κ₁ := by
  rw [parallelComp_id_left_comp_parallelComp]
  congr
  exact comp_id κ₁

@[simp]
lemma comp_parallelComp_id {ι γ : Type*} [MeasurableSpace ι] [MeasurableSpace γ] (κ₁ : Kernel α β)
    (κ₂ : Kernel ι γ) [IsSFiniteKernel κ₁] [IsSFiniteKernel κ₂] :
    κ₁ ∥ₖ Kernel.id ∘ₖ (Kernel.id ∥ₖ κ₂) = κ₁ ∥ₖ κ₂ := by
  rw [parallelComp_id_right_comp_parallelComp]
  congr
  exact comp_id κ₁

lemma id_eq_deterministic_id :
    (Kernel.id : Kernel α α) = Kernel.deterministic id measurable_id := by
  ext x s hs
  simp [Kernel.deterministic_apply, Kernel.id_apply]

end ProbabilityTheory.Kernel
