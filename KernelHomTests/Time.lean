/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import KernelHom
public import Mathlib.Probability.Kernel.Composition.KernelLemmas

/-!
# Timing of Kernel-Hom proofs

Each lemma is proved twice: with its original Mathlib proof (`_orig`) and with Kernel-Hom (`_kh`).
Only lemmas whose Mathlib proof is a complete proof by integral manipulations are kept, so that the
comparison is meaningful. `trace.profiler` reports the elaboration time of each declaration.
-/

public section

open MeasureTheory ProbabilityTheory Kernel CategoryTheory

set_option trace.profiler true
set_option trace.profiler.threshold 10

variable {X Y Z T X' Y' Z' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace Z] [MeasurableSpace T] [MeasurableSpace X'] [MeasurableSpace Y']
  [MeasurableSpace Z']

variable {κ : Kernel X Y} {ξ : Kernel Z T} {η : Kernel Y Z}

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

lemma swap_parallelComp_kh : swap Y T ∘ₖ (κ ∥ₖ ξ) = ξ ∥ₖ κ ∘ₖ swap X Z := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  by_cases hη : IsSFiniteKernel ξ
  swap; · simp [hη]
  kernel_hom
  aesop_cat

variable [IsSFiniteKernel η] [IsSFiniteKernel ξ]

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

lemma parallelComp_id_left_comp_parallelComp_kh :
    (Kernel.id ∥ₖ ξ) ∘ₖ (κ ∥ₖ η) = κ ∥ₖ (ξ ∘ₖ η) := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  kernel_monoidal
