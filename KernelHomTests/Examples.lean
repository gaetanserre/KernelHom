/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import KernelHom.Tactic.Tactics

/-!
# Examples for Kernel-Hom
-/

@[expose] public section

open MeasureTheory ProbabilityTheory CategoryTheory BraidedCategory

open scoped MonoidalCategory ComonObj KernelHom

show_panel_widgets [local KernelDiagram]

variable {X Y Z T X' Y' Z' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace Z] [MeasurableSpace T] [MeasurableSpace X'] [MeasurableSpace Y']
  [MeasurableSpace Z']

namespace ProbabilityTheory.Kernel

variable {κ : Kernel X Y} {ξ : Kernel Z T} {η : Kernel Y Z}

lemma swap_parallelComp₀ : swap Y T ∘ₖ (κ ∥ₖ ξ) = ξ ∥ₖ κ ∘ₖ swap X Z := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  by_cases hη : IsSFiniteKernel ξ
  swap; · simp [hη]
  kernel_hom
  cat_disch

lemma swap_parallelComp_diag [IsSFiniteKernel κ] [IsSFiniteKernel ξ] :
    swap Y T ∘ₖ (κ ∥ₖ ξ) = ξ ∥ₖ κ ∘ₖ swap X Z := by
  kernel_hom
  cat_disch

variable [IsSFiniteKernel η] [IsSFiniteKernel ξ]

lemma parallelComp_id_left_comp_parallelComp₀ :
    (Kernel.id ∥ₖ ξ) ∘ₖ (κ ∥ₖ η) = κ ∥ₖ (ξ ∘ₖ η) := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  kernel_monoidal

lemma parallelComp_id_left_comp_parallelComp_diag [IsSFiniteKernel κ] :
    (Kernel.id ∥ₖ ξ) ∘ₖ (κ ∥ₖ η) = κ ∥ₖ (ξ ∘ₖ η) := by
  kernel_monoidal

lemma parallelComp_id_right_comp_parallelComp₀ :
    (ξ ∥ₖ Kernel.id) ∘ₖ (η ∥ₖ κ) = (ξ ∘ₖ η) ∥ₖ κ := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  kernel_monoidal

lemma parallelComp_id_right_comp_parallelComp_diag [IsSFiniteKernel κ] :
    (ξ ∥ₖ Kernel.id) ∘ₖ (η ∥ₖ κ) = (ξ ∘ₖ η) ∥ₖ κ := by
  kernel_monoidal

variable [IsSFiniteKernel κ]

variable {κ' : Kernel X Y'} {η' : Kernel Y' Z'} [IsSFiniteKernel κ'] [IsSFiniteKernel η']

lemma parallelComp_comp_parallelComp₀ :
    (η ∥ₖ η') ∘ₖ (κ ∥ₖ κ') = (η ∘ₖ κ) ∥ₖ (η' ∘ₖ κ') := by
  kernel_monoidal

lemma parallelComp_comp_prod₀ :
    (η ∥ₖ η') ∘ₖ (κ ×ₖ κ') = (η ∘ₖ κ) ×ₖ (η' ∘ₖ κ') := by
  kernel_monoidal

lemma discard_comp_deterministic {f : X → Y} (hf : Measurable f) :
    discard Y ∘ₖ (deterministic f hf) = discard X := by
  kernel_hom
  simp only [IsComonHom.hom_counit]

variable {κ : Kernel (X × Y) Z}

lemma parallelComp_self_comp_copy₀ [IsMarkovKernel κ] [IsDeterministic κ] :
    (κ ∥ₖ κ) ∘ₖ copy (X × Y) = copy Z ∘ₖ κ := by
  kernel_disch


end ProbabilityTheory.Kernel
