/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Probability.Kernel.Composition.CompProd
public import Mathlib.Probability.Kernel.Composition.ParallelComp
public import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Kernel utilities

This file provides helper lemmas for working with kernels.

## Main declarations

* `comap_parallelComp_comap`: the comap of a parallel composition is the parallel composition of
  the comaps.
* `map_parallelComp_map`: the map of a parallel composition is the parallel composition of the maps.
* `comp_parallelComp_comp_copy_eq_comp_prod`, `comp_compProd_def_eq_comp_compProd`: fold a product
  `×ₖ` and a composition-product `⊗ₖ` preceded by a kernel `ξ`, in the left-associated form of
  the compositions.
-/

@[expose] public section

open ProbabilityTheory MeasureTheory

variable {α β γ ι : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace ι]

namespace ProbabilityTheory.Kernel

lemma comap_parallelComp_comap {α₂ γ₂ : Type*} [MeasurableSpace α₂] [MeasurableSpace γ₂]
    (κ : Kernel α β) (η : Kernel γ ι) [IsSFiniteKernel κ] [IsSFiniteKernel η]
    {f : α₂ → α} {g : γ₂ → γ} (hf : Measurable f) (hg : Measurable g) :
    κ.comap f hf ∥ₖ η.comap g hg = (κ ∥ₖ η).comap (fun a ↦ (f a.1, g a.2)) (by fun_prop) := by
  ext : 1
  rw [Kernel.parallelComp_apply, Kernel.comap_apply, Kernel.comap_apply, Kernel.comap_apply,
    Kernel.parallelComp_apply]

lemma map_parallelComp_map {β₂ ι₂ : Type*} [MeasurableSpace β₂] [MeasurableSpace ι₂]
    (κ : Kernel α β) (η : Kernel γ ι) [IsSFiniteKernel κ] [IsSFiniteKernel η]
    {f : β → β₂} {g : ι → ι₂} (hf : Measurable f) (hg : Measurable g) :
    κ.map f ∥ₖ η.map g = (κ ∥ₖ η).map (fun a ↦ (f a.1, g a.2)) := by
  ext a s hs
  rw [Kernel.parallelComp_apply', Kernel.lintegral_map, Kernel.map_apply',
    Kernel.parallelComp_apply']
  · congr with x
    rw [Kernel.map_apply' _ (by fun_prop) _ (by measurability)]
    congr
  all_goals try fun_prop
  all_goals try measurability
  exact measurable_measure_prodMk_left hs

/-! The compositions of kernels associate to the left, so that a product preceded by a kernel `ξ`
is written `ξ ∘ₖ (κ ∥ₖ η) ∘ₖ copy α` once unfolded, which does not contain the unfolding
`(κ ∥ₖ η) ∘ₖ copy α` of `κ ×ₖ η` as a subterm. The following lemmas fold the products and
composition-products in this form; together with `parallelComp_comp_copy` and `compProd_def`, they
fold all of them in a left-associated composition of kernels. -/

/-- Fold a product `×ₖ` preceded by a kernel `ξ`. -/
lemma comp_parallelComp_comp_copy_eq_comp_prod {δ : Type*} [MeasurableSpace δ]
    (ξ : Kernel (β × γ) δ) (κ : Kernel α β) (η : Kernel α γ) :
    ξ ∘ₖ (κ ∥ₖ η) ∘ₖ copy α = ξ ∘ₖ (κ ×ₖ η) := by
  rw [comp_assoc, parallelComp_comp_copy]

/-- Fold a composition-product `⊗ₖ` preceded by a kernel `ξ`. -/
lemma comp_compProd_def_eq_comp_compProd {δ : Type*} [MeasurableSpace δ]
    (ξ : Kernel (β × γ) δ) (κ : Kernel α β) (η : Kernel (α × β) γ) :
    ξ ∘ₖ swap γ β ∘ₖ (η ∥ₖ Kernel.id)
        ∘ₖ deterministic MeasurableEquiv.prodAssoc.symm (MeasurableEquiv.measurable _)
        ∘ₖ (Kernel.id ∥ₖ copy β) ∘ₖ (Kernel.id ∥ₖ κ) ∘ₖ copy α = ξ ∘ₖ (κ ⊗ₖ η) := by
  rw [compProd_def]
  simp only [comp_assoc]

end ProbabilityTheory.Kernel
