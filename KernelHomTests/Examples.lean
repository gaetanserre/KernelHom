/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import KernelHom

/-!
# Structural lemmas of Mathlib

Lemmas of `Mathlib.Probability.Kernel.Composition` that are equalities of kernels built only from
composition, parallel composition, product, identity, copy and swap, and that are not used to build
the category `SFinKer`. The other lemmas of this kind, such as `Kernel.comp_assoc` or
`Kernel.swap_parallelComp`, are used to prove the axioms of `SFinKer`, so their proofs with
Kernel-Hom could not replace the ones of Mathlib. Each lemma has the name of its Mathlib
counterpart, suffixed by `₀`.

They are all proved by a single call to `kernel_monoidal` or `kernel_disch`, which also handles the
exchange law (`parallelComp_comm₀`) and the coassociativity of copy (`prodAssoc_prod₀`).

`Kernel.map` is not translated, so `map_prod_swap₀` and `prodAssoc_prod₀` are first rewritten with
`swap_comp_eq_map` and `deterministic_comp_eq_map`. As in Mathlib, `parallelComp_comm₀` holds for
any kernels, and the case of a non s-finite kernel is closed by `simp`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory CategoryTheory MonoidalCategory

open scoped KernelHom

show_panel_widgets [local KernelDiagram]

variable {X Y Z T Y' Z' : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  [MeasurableSpace T] [MeasurableSpace Y'] [MeasurableSpace Z']

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

/-! ### `Mathlib.Probability.Kernel.Composition.KernelLemmas` -/

lemma parallelComp_comp_prod₀ {κ : Kernel X Y} [IsSFiniteKernel κ] {η : Kernel Y Z}
    [IsSFiniteKernel η] {κ' : Kernel X Y'} [IsSFiniteKernel κ'] {η' : Kernel Y' Z'}
    [IsSFiniteKernel η'] :
    (η ∥ₖ η') ∘ₖ (κ ×ₖ κ') = (η ∘ₖ κ) ×ₖ (η' ∘ₖ κ') := by
  kernel_monoidal

lemma parallelComp_comm₀ {κ : Kernel X Y} {η : Kernel Z T} :
    (Kernel.id ∥ₖ κ) ∘ₖ (η ∥ₖ Kernel.id) = (η ∥ₖ Kernel.id) ∘ₖ (Kernel.id ∥ₖ κ) := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  by_cases hη : IsSFiniteKernel η
  swap; · simp [hη]
  kernel_disch

end ProbabilityTheory.Kernel
