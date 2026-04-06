/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import KernelHom.Tactic.Tactics
import Mathlib.Probability.Kernel.Posterior

/-!

# Posterior kernel

For `μ : Measure Ω` (called prior measure), seen as a measure on a parameter, and a kernel
`κ : Kernel Ω 𝓧` that gives the conditional distribution of "data" in `𝓧` given the prior parameter,
we can get the distribution of the data with `κ ∘ₘ μ`, and the joint distribution of parameter and
data with `μ ⊗ₘ κ : Measure (Ω × 𝓧)`.

The posterior distribution of the parameter given the data is a Markov kernel `κ†μ : Kernel 𝓧 Ω`
such that `(κ ∘ₘ μ) ⊗ₘ κ†μ = (μ ⊗ₘ κ).map Prod.swap`. That is, the joint distribution of parameter
and data can be recovered from the distribution of the data and the posterior.

## Main definitions

* `posterior κ μ`: posterior of a kernel `κ` for a prior measure `μ`.

## Main statements

* `compProd_posterior_eq_map_swap`: the main property of the posterior,
  `(κ ∘ₘ μ) ⊗ₘ κ†μ = (μ ⊗ₘ κ).map Prod.swap`.
* `ae_eq_posterior_of_compProd_eq`
* `posterior_comp_self`: `κ†μ ∘ₘ κ ∘ₘ μ = μ`
* `posterior_posterior`: `(κ†μ)†(κ ∘ₘ μ) =ᵐ[μ] κ`
* `posterior_comp`: `(η ∘ₖ κ)†μ =ᵐ[η ∘ₘ κ ∘ₘ μ] κ†μ ∘ₖ η†(κ ∘ₘ μ)`

* `posterior_eq_withDensity`: If `κ ω ≪ κ ∘ₘ μ` for `μ`-almost every `ω`,
  then for `κ ∘ₘ μ`-almost every `x`,
  `κ†μ x = μ.withDensity (fun ω ↦ κ.rnDeriv (Kernel.const _ (κ ∘ₘ μ)) ω x)`.
  The condition is true for countable `Ω`: see `absolutelyContinuous_comp_of_countable`.

## Notation

`κ†μ` denotes the posterior of `κ` with respect to `μ`, `posterior κ μ`.
`†` can be typed as `\dag` or `\dagger`.

This notation emphasizes that the posterior is a kind of inverse of `κ`, which we would want to
denote `κ†`, but we have to also specify the measure `μ`.

-/

open scoped ENNReal

open MeasureTheory CategoryTheory
open scoped MonoidalCategory ComonObj

open MonoidalCategory in
lemma CategoryTheory.tensorObjSFinker {X Y : SFinKer} :
    X ⊗ Y = SFinKer.of (X.carrier × Y.carrier) := rfl

namespace ProbabilityTheory

variable {Ω 𝓧 𝓨 𝓩 : Type*} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧}
    {m𝓨 : MeasurableSpace 𝓨} {m𝓩 : MeasurableSpace 𝓩}
    {κ : Kernel Ω 𝓧} {μ : Measure Ω} [IsFiniteMeasure μ] [IsFiniteKernel κ]

variable [StandardBorelSpace Ω] [Nonempty Ω]

lemma const_ext_measure {α : Type*} [MeasurableSpace α] (μ ν : Measure α) :
    μ = ν ↔ Kernel.const Unit μ = Kernel.const Unit ν := by
  constructor
  · intro h
    rw [h]
  · intro h
    replace h := DFunLike.congr (x := ()) h rfl
    simpa using h

lemma parallelProd_posterior_comp_copy_comp' :
    (Kernel.id ∥ₖ κ†μ) ∘ₘ Kernel.copy 𝓧 ∘ₘ κ ∘ₘ μ
      = (κ ∥ₖ Kernel.id) ∘ₘ Kernel.copy Ω ∘ₘ μ := by
  rw [const_ext_measure]
  simp only [← Kernel.comp_const]
  kernel_monoidal
  simp only [tensorObjSFinker, Iso.trans_refl, Iso.refl_hom, MonoidalCategory.whiskerLeftIso_refl,
    Category.comp_id, Category.id_comp, MonoidalCategory.whiskerRightIso_refl]
  hom_kernel
  simp only [Kernel.parallelComp_comp_copy]
  ext a s hs
  rw [Kernel.prod_apply' _ _ _ hs]
  simp_rw [Kernel.id_apply, Measure.dirac_apply]
  rw [Kernel.comp_apply' _ _ _ hs]
  have : ∀ (b : 𝓧), ((Kernel.id ×ₖ κ†μ) b) s = ((κ†μ) b) (Prod.mk b ⁻¹' s) := by
    intro b
    rw [Kernel.id_prod_apply' _ _ hs]
  simp_rw [this]
  sorry

end ProbabilityTheory
