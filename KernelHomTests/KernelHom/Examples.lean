/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import KernelHom

/-!
# Examples

This file contains the examples of the paper *Categorical reasoning for probability kernels in
Mathlib* and of the manual.

* Lemmas of Mathlib about kernels, proved with the tactics. Each of them has the name of its
  Mathlib counterpart, suffixed by `₀`.
* Examples of `kernel_hom`, `hom_kernel` and `@[kernel_reassoc]`.
* Equalities that `kernel_disch` does not prove.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory CategoryTheory MonoidalCategory ComonObj

open scoped KernelHom

show_panel_widgets [local KernelDiagram]

variable {X Y Z T W Y' Z' : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  [MeasurableSpace T] [MeasurableSpace W] [MeasurableSpace Y'] [MeasurableSpace Z']

namespace ProbabilityTheory.Kernel

/-! ### `Mathlib.Probability.Kernel.Composition.Prod` -/

lemma map_prod_swap₀ (κ : Kernel X Y) (η : Kernel X Z) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    map (κ ×ₖ η) Prod.swap = η ×ₖ κ := by
  rw [← swap_comp_eq_map]
  kernel_disch

lemma swap_prod₀ {κ : Kernel X Y} [IsSFiniteKernel κ] {η : Kernel X Z} [IsSFiniteKernel η] :
    swap Y Z ∘ₖ (κ ×ₖ η) = η ×ₖ κ := by
  kernel_disch

lemma prodAssoc_prod₀ (κ : Kernel X Y) [IsSFiniteKernel κ] (η : Kernel X Z) [IsSFiniteKernel η]
    (ξ : Kernel X T) [IsSFiniteKernel ξ] :
    ((κ ×ₖ ξ) ×ₖ η).map MeasurableEquiv.prodAssoc = κ ×ₖ (ξ ×ₖ η) := by
  rw [← deterministic_comp_eq_map (MeasurableEquiv.measurable _)]
  kernel_disch

lemma prodAssoc_symm_prod₀ (κ : Kernel X Y) [IsSFiniteKernel κ] (η : Kernel X Z)
    [IsSFiniteKernel η] (ξ : Kernel X T) [IsSFiniteKernel ξ] :
    (κ ×ₖ (ξ ×ₖ η)).map MeasurableEquiv.prodAssoc.symm = (κ ×ₖ ξ) ×ₖ η := by
  rw [← deterministic_comp_eq_map (MeasurableEquiv.measurable _)]
  kernel_disch

lemma prodComm_prod₀ {κ : Kernel X Y} [IsSFiniteKernel κ] {η : Kernel X Z} [IsSFiniteKernel η] :
    (κ ×ₖ η).map MeasurableEquiv.prodComm = η ×ₖ κ := by
  rw [show ⇑(MeasurableEquiv.prodComm : Y × Z ≃ᵐ Z × Y) = Prod.swap from rfl,
    ← swap_comp_eq_map]
  kernel_disch

/-! ### `Mathlib.Probability.Kernel.Composition.KernelLemmas` -/

@[kernel_reassoc]
lemma parallelComp_comp_prod₀ (κ : Kernel X Y) [IsSFiniteKernel κ] (η : Kernel Y Z)
    [IsSFiniteKernel η] (κ' : Kernel X Y') [IsSFiniteKernel κ'] (η' : Kernel Y' Z')
    [IsSFiniteKernel η'] :
    (η ∥ₖ η') ∘ₖ (κ ×ₖ κ') = (η ∘ₖ κ) ×ₖ (η' ∘ₖ κ') := by
  kernel_disch

lemma parallelComp_comm₀ {κ : Kernel X Y} {η : Kernel Z T} :
    (Kernel.id ∥ₖ κ) ∘ₖ (η ∥ₖ Kernel.id) = (η ∥ₖ Kernel.id) ∘ₖ (Kernel.id ∥ₖ κ) := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  by_cases hη : IsSFiniteKernel η
  swap; · simp [hη]
  kernel_disch

/-! ### `Mathlib.Probability.Kernel.Deterministic` -/

lemma parallelComp_self_comp_copy₀ (κ : Kernel (X × Y) Z) [IsMarkovKernel κ]
    [IsDeterministic κ] :
    (κ ∥ₖ κ) ∘ₖ copy (X × Y) = copy Z ∘ₖ κ := by
  kernel_disch

/-! ### Translation to `SFinKer` and back -/

example {κ : Kernel X Y} [IsSFiniteKernel κ] {η : Kernel X Z} [IsSFiniteKernel η] :
    swap Y Z ∘ₖ (κ ×ₖ η) = η ×ₖ κ := by
  kernel_hom
  -- ⊢ (Δ ≫ (κ ⊗ₘ η)) ≫ (β_ Y Z).hom = Δ ≫ (η ⊗ₘ κ)
  cat_disch

example (κ : Kernel Y Z) [IsSFiniteKernel κ] (f : X → Y) (hf : Measurable f) :
    swap Z Z ∘ₖ copy Z ∘ₖ κ ∘ₖ deterministic f hf =
      copy Z ∘ₖ κ.comap f hf := by
  kernel_hom
  -- ⊢ deterministic f hf ≫ κ ≫ Δ ≫ (β_ Z Z).hom = κ.comap f hf ≫ Δ
  simp only [IsCommComonObj.comul_comm]
  hom_kernel
  -- ⊢ copy Z ∘ₖ κ ∘ₖ deterministic f hf = copy Z ∘ₖ κ.comap f hf
  rw [Kernel.comp_assoc, Kernel.comp_deterministic_eq_comap]

/-! ### `@[kernel_reassoc]` and `kernel_reassoc_of%` -/

example (κ : Kernel X Y) [IsSFiniteKernel κ] (η : Kernel Y Z) [IsSFiniteKernel η]
    (κ' : Kernel X Y') [IsSFiniteKernel κ'] (η' : Kernel Y' Z') [IsSFiniteKernel η']
    (ξ : Kernel (Z × Z') W) [IsSFiniteKernel ξ] :
    ξ ∘ₖ (η ∥ₖ η') ∘ₖ (κ ×ₖ κ') = ξ ∘ₖ ((η ∘ₖ κ) ×ₖ (η' ∘ₖ κ')) := by
  rw [parallelComp_comp_prod₀_assoc]

example (κ : Kernel X Y) [IsSFiniteKernel κ] (η : Kernel Y Z) [IsSFiniteKernel η]
    (ζ : Kernel X Z) [IsSFiniteKernel ζ] (ξ : Kernel Z W) [IsSFiniteKernel ξ]
    (h : η ∘ₖ κ = ζ) :
    ξ ∘ₖ η ∘ₖ κ = ξ ∘ₖ ζ := by
  rw [kernel_reassoc_of% h]

/-! ### Limitations -/

/-- The marginals are not translated. -/
example (κ : Kernel X Y) [IsSFiniteKernel κ] (η : Kernel X Z) [IsMarkovKernel η] :
    fst (κ ×ₖ η) = κ := by
  fail_if_success kernel_disch
  exact fst_prod κ η

/-- The inverse unitors are only recognized by `hom_kernel`. -/
example (κ : Kernel Z Y) [IsSFiniteKernel κ] :
    (Kernel.discard.{_, 0} Z ∥ₖ κ) ∘ₖ Kernel.copy Z = (Kernel.id.map fun x ↦ ((), x)) ∘ₖ κ := by
  fail_if_success kernel_disch
  kernel_hom
  simp only [ComonObj.counit_comul_hom]
  hom_kernel
  rfl

/-- Positivity is not used by `kernel_disch`. -/
example (κ : Kernel X Y) [IsMarkovKernel κ] (η : Kernel Y Z) [IsMarkovKernel η]
    [IsDeterministic (η ∘ₖ κ)] :
    ((η ∘ₖ κ) ∥ₖ κ) ∘ₖ copy X = (η ∥ₖ Kernel.id) ∘ₖ copy Y ∘ₖ κ := by
  fail_if_success kernel_disch
  exact comp_parallelComp_comp_copy

end ProbabilityTheory.Kernel
