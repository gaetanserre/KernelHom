/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import KernelHom
public import Mathlib.Probability.Kernel.Composition.KernelLemmas
public import Mathlib.Util.CountHeartbeats

/-!
# Heartbeats of Kernel-Hom proofs

Each lemma of `KernelHomTests.Examples` is reproduced here together with its Mathlib proof
(`_orig`), and `#count_heartbeats!` reports the number of heartbeats used by each proof, a
deterministic measure of the work done by the elaborator.
-/

public section

open MeasureTheory ProbabilityTheory CategoryTheory BraidedCategory

open scoped MonoidalCategory ComonObj KernelHom

variable {X Y Z T X' Y' Z' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace Z] [MeasurableSpace T] [MeasurableSpace X'] [MeasurableSpace Y']
  [MeasurableSpace Z']

namespace ProbabilityTheory.Kernel

variable {κ : Kernel X Y} {ξ : Kernel Z T} {η : Kernel Y Z}

#count_heartbeats! in
lemma swap_parallelComp_orig : swap Y T ∘ₖ (κ ∥ₖ ξ) = ξ ∥ₖ κ ∘ₖ swap X Z := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  by_cases hη : IsSFiniteKernel ξ
  swap; · simp [hη]
  ext ac s hs
  simp_rw [comp_apply, parallelComp_apply, Measure.bind_apply hs (Kernel.aemeasurable _),
    swap_apply, lintegral_dirac' _ (Kernel.measurable_coe _ hs), parallelComp_apply' hs,
    Prod.fst_swap, Prod.snd_swap]
  rw [MeasureTheory.lintegral_prod_symm]
  swap; · exact ((Kernel.id.measurable_coe hs).comp measurable_swap).aemeasurable
  congr with d
  simp_rw [Prod.swap_prod_mk, Measure.dirac_apply' _ hs, ← Set.indicator_comp_right,
    lintegral_indicator (measurable_prodMk_left hs)]
  simp

#count_heartbeats! in
lemma swap_parallelComp₀ : swap Y T ∘ₖ (κ ∥ₖ ξ) = ξ ∥ₖ κ ∘ₖ swap X Z := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  by_cases hη : IsSFiniteKernel ξ
  swap; · simp [hη]
  kernel_hom
  cat_disch

variable [IsSFiniteKernel η] [IsSFiniteKernel ξ]

#count_heartbeats! in
lemma parallelComp_id_left_comp_parallelComp_orig :
    (Kernel.id ∥ₖ ξ) ∘ₖ (κ ∥ₖ η) = κ ∥ₖ (ξ ∘ₖ η) := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  ext a s hs
  rw [comp_apply' _ _ _ hs, parallelComp_apply,
    MeasureTheory.lintegral_prod _ (Kernel.measurable_coe _ hs).aemeasurable]
  rw [parallelComp_apply, Measure.prod_apply hs]
  congr with x
  rw [comp_apply' _ _ _ (measurable_prodMk_left hs)]
  congr with y
  rw [parallelComp_apply' hs, Kernel.id_apply,
    lintegral_dirac' _ (measurable_measure_prodMk_left hs)]

#count_heartbeats! in
lemma parallelComp_id_left_comp_parallelComp₀ :
    (Kernel.id ∥ₖ ξ) ∘ₖ (κ ∥ₖ η) = κ ∥ₖ (ξ ∘ₖ η) := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  kernel_monoidal

#count_heartbeats! in
lemma parallelComp_id_right_comp_parallelComp_orig :
    (ξ ∥ₖ Kernel.id) ∘ₖ (η ∥ₖ κ) = (ξ ∘ₖ η) ∥ₖ κ := by
  suffices swap T Y ∘ₖ (ξ ∥ₖ Kernel.id) ∘ₖ (η ∥ₖ κ) = swap T Y ∘ₖ ((ξ ∘ₖ η) ∥ₖ κ) by
    calc ξ ∥ₖ Kernel.id ∘ₖ (η ∥ₖ κ)
    _ = swap Y T ∘ₖ (swap T Y ∘ₖ (ξ ∥ₖ Kernel.id) ∘ₖ (η ∥ₖ κ)) := by
      simp_rw [← comp_assoc, swap_swap, id_comp]
    _ = swap Y T ∘ₖ (swap T Y ∘ₖ ((ξ ∘ₖ η) ∥ₖ κ)) := by rw [this]
    _ = ξ ∘ₖ η ∥ₖ κ := by simp_rw [← comp_assoc, swap_swap, id_comp]
  simp_rw [swap_parallelComp, comp_assoc, swap_parallelComp, ← comp_assoc,
    parallelComp_id_left_comp_parallelComp]

#count_heartbeats! in
lemma parallelComp_id_right_comp_parallelComp₀ :
    (ξ ∥ₖ Kernel.id) ∘ₖ (η ∥ₖ κ) = (ξ ∘ₖ η) ∥ₖ κ := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  kernel_monoidal

variable [IsSFiniteKernel κ]

variable {κ' : Kernel X Y'} {η' : Kernel Y' Z'} [IsSFiniteKernel κ'] [IsSFiniteKernel η']

#count_heartbeats! in
lemma parallelComp_comp_parallelComp_orig :
    (η ∥ₖ η') ∘ₖ (κ ∥ₖ κ') = (η ∘ₖ κ) ∥ₖ (η' ∘ₖ κ') := by
  rw [← parallelComp_id_left_comp_parallelComp, ← parallelComp_id_right_comp_parallelComp,
    ← comp_assoc, parallelComp_id_left_comp_parallelComp, comp_id]

#count_heartbeats! in
lemma parallelComp_comp_parallelComp₀ :
    (η ∥ₖ η') ∘ₖ (κ ∥ₖ κ') = (η ∘ₖ κ) ∥ₖ (η' ∘ₖ κ') := by
  kernel_monoidal

#count_heartbeats! in
lemma parallelComp_comp_prod_orig :
    (η ∥ₖ η') ∘ₖ (κ ×ₖ κ') = (η ∘ₖ κ) ×ₖ (η' ∘ₖ κ') := by
  rw [← parallelComp_comp_copy, ← comp_assoc, parallelComp_comp_parallelComp,
    ← parallelComp_comp_copy]

#count_heartbeats! in
lemma parallelComp_comp_prod₀ :
    (η ∥ₖ η') ∘ₖ (κ ×ₖ κ') = (η ∘ₖ κ) ×ₖ (η' ∘ₖ κ') := by
  kernel_monoidal

#count_heartbeats! in
lemma discard_comp_deterministic_orig {f : X → Y} (hf : Measurable f) :
    discard Y ∘ₖ (deterministic f hf) = discard X :=
  comp_discard _

#count_heartbeats! in
lemma discard_comp_deterministic {f : X → Y} (hf : Measurable f) :
    discard Y ∘ₖ (deterministic f hf) = discard X := by
  kernel_hom
  simp only [IsComonHom.hom_counit]

variable (κ : Kernel (X × Y) Z)

#count_heartbeats! in
lemma parallelComp_self_comp_copy_orig [IsMarkovKernel κ] [IsDeterministic κ] :
    (κ ∥ₖ κ) ∘ₖ copy (X × Y) = copy Z ∘ₖ κ :=
  parallelComp_self_comp_copy

#count_heartbeats! in
lemma parallelComp_self_comp_copy₀ [IsMarkovKernel κ] [IsDeterministic κ] :
    (κ ∥ₖ κ) ∘ₖ copy (X × Y) = copy Z ∘ₖ κ := by
  kernel_disch

end ProbabilityTheory.Kernel

end
