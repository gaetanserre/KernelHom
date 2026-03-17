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

/-- The Markov kernel to the universe-polymorphic type `PUnit`. -/
noncomputable
def Pdiscard (X : Type*) [MeasurableSpace X] : Kernel X PUnit :=
  Kernel.deterministic (fun _ ↦ PUnit.unit) measurable_const

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

instance : IsMarkovKernel (Pdiscard X) := by rw [Pdiscard]; infer_instance

@[simp]
lemma comp_Pdiscard (κ : Kernel X Y) [IsMarkovKernel κ] : (Pdiscard Y) ∘ₖ κ = Pdiscard X := by
  ext _ _ hs
  simp [comp_apply' _ _ _ hs, Pdiscard, deterministic_apply]

@[simp]
lemma Pdiscard_apply (a : X) : Pdiscard X a = Measure.dirac PUnit.unit := by
  simp [Pdiscard, deterministic_apply]

@[simp]
lemma parallelComp_id_id :
    Kernel.id ∥ₖ Kernel.id = (Kernel.id : Kernel (X × Y) (X × Y)) := by
  ext : 1
  simp [parallelComp_apply, id_apply, Measure.dirac_prod_dirac]

@[simp]
lemma parallelComp_id_id_comp_parallelComp_id_id :
    (Kernel.id ∥ₖ Kernel.id) ∘ₖ (Kernel.id ∥ₖ Kernel.id)
      = (Kernel.id : Kernel (X × Y) (X × Y)) := by
  rw [parallelComp_id_id]
  simp only [comp_id]

lemma parallelComp_id_id_map {Z : Type*} [MeasurableSpace Z] {f : X → Y} (hf : Measurable f) :
   Kernel.id ∥ₖ Kernel.id.map f =
    (Kernel.id.map (fun x => (x.1, f x.2)) : Kernel (Z × X) (Z × Y)) := by
  rw [id_map hf, id_map (by fun_prop)]
  ext : 1
  simp [parallelComp_apply, id_apply, deterministic_apply, Measure.dirac_prod_dirac]

lemma parallelComp_id_map_id {Z : Type*} [MeasurableSpace Z] {f : X → Y} (hf : Measurable f) :
   Kernel.id.map f ∥ₖ Kernel.id =
    (Kernel.id.map (fun x => (f x.1, x.2)) : Kernel (X × Z) (Y × Z)) := by
  rw [id_map hf, id_map (by fun_prop)]
  ext : 1
  simp [parallelComp_apply, id_apply, deterministic_apply, Measure.dirac_prod_dirac]

@[simp]
lemma comp_id_parallelComp {Z γ : Type*} [MeasurableSpace Z] [MeasurableSpace γ] (κ₁ : Kernel X Y)
    (κ₂ : Kernel Z γ) [IsSFiniteKernel κ₁] [IsSFiniteKernel κ₂] :
    Kernel.id ∥ₖ κ₁ ∘ₖ (κ₂ ∥ₖ Kernel.id) = κ₂ ∥ₖ κ₁ := by
  rw [parallelComp_id_left_comp_parallelComp]
  congr
  exact comp_id κ₁

@[simp]
lemma comp_parallelComp_id {Z γ : Type*} [MeasurableSpace Z] [MeasurableSpace γ] (κ₁ : Kernel X Y)
    (κ₂ : Kernel Z γ) [IsSFiniteKernel κ₁] [IsSFiniteKernel κ₂] :
    κ₁ ∥ₖ Kernel.id ∘ₖ (Kernel.id ∥ₖ κ₂) = κ₁ ∥ₖ κ₂ := by
  rw [parallelComp_id_right_comp_parallelComp]
  congr
  exact comp_id κ₁

end ProbabilityTheory.Kernel
