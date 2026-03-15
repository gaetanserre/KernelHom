/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Mathlib.CategoryTheory.MarkovCategory.Basic
import Mathlib.MeasureTheory.Category.MeasCat
import LeanStoch.Tactic.SFinite
import LeanStoch.Mathlib.Kernel

/-!
# The symmetric monoidal category Stoch

This file defines the category **Stoch** of measurable spaces and s-finite kernels,
and proves it is a symmetric monoidal category.

## Main definitions

* `Stoch`: the category whose objects are measurable spaces and morphisms are s-finite kernels
* `instance : MonoidalCategory Stoch`: **Stoch** has a monoidal structure
* `instance : SymmetricCategory Stoch`: **Stoch** is a symmetric monoidal category

## Implementation notes

Morphisms in **Stoch** are represented as subtypes `{ k : Kernel X Y // IsSFiniteKernel k }`.
The monoidal structure is given by the categorical product of measurable spaces.

## References

* [Tobias Fritz, A synthetic approach to Markov kernels, conditional independence and theorems on sufficient statistics](https://arxiv.org/abs/1908.07021)
-/

open CategoryTheory ProbabilityTheory MeasureTheory

universe u

/-- The category **Stoch** of measurable spaces and Markov kernels. -/
structure Stoch : Type (u + 1) where
  of ::
  carrier : Type u
  [str : MeasurableSpace carrier]

attribute [instance] Stoch.str

instance : CoeSort Stoch Type* :=
  ⟨Stoch.carrier⟩

noncomputable section

/-- **Stoch** is a large category with Markov kernels as morphisms.
Composition is given by kernel composition `∘ₖ`. -/
instance : LargeCategory Stoch.{u} where
  Hom X Y := { k : Kernel X Y // IsSFiniteKernel k }
  id X := ⟨Kernel.id, by kernel_sfinite⟩
  comp κ₁ κ₂ := ⟨κ₂.1 ∘ₖ κ₁.1, by kernel_sfinite⟩
  assoc κ₁ κ₂ κ₃ := by simp [Kernel.comp_assoc]

/-- **Stoch** is a monoidal category with tensor product given by the categorical product.
The unit is the terminal object `Unit`. -/
instance : MonoidalCategory Stoch.{u} where
  tensorObj X Y := Stoch.of (X × Y)
  whiskerLeft X Y₁ Y₂ κ := ⟨Kernel.id ∥ₖ κ.1, by kernel_sfinite⟩
  whiskerRight κ Y := ⟨κ.1 ∥ₖ Kernel.id, by kernel_sfinite⟩
  tensorUnit := Stoch.of PUnit
  associator X Y Z := by
    let f₁ := fun (x : (X × Y) × Z) ↦ (x.1.1, x.1.2, x.2)
    let f₂ := fun (x : X × Y × Z) ↦ ((x.1, x.2.1), x.2.2)
    have hf₁ : Measurable f₁ := by fun_prop
    have hf₂ : Measurable f₂ := by fun_prop
    refine ⟨⟨Kernel.id.map f₁, by kernel_sfinite⟩,
      ⟨Kernel.id.map f₂, by kernel_sfinite⟩, ?_, ?_⟩
    · cat_kernel
      rw [Kernel.id_map hf₁, Kernel.id_map hf₂, Kernel.deterministic_comp_eq_map hf₂,
        Kernel.deterministic_map hf₁ hf₂]
      ext : 1
      simp [Kernel.deterministic_apply, Kernel.id_apply, f₁, f₂]
    · cat_kernel
      rw [Kernel.id_map hf₂, Kernel.id_map hf₁, Kernel.deterministic_comp_eq_map hf₁,
        Kernel.deterministic_map hf₂ hf₁]
      ext : 1
      simp [Kernel.deterministic_apply, Kernel.id_apply, f₁, f₂]
  leftUnitor X := by
    let f₁ := fun (x : X) ↦ (PUnit.unit, x)
    have hf₁ : Measurable f₁ := by fun_prop
    have hf₂ : Measurable (Prod.snd : PUnit × X → X) := by fun_prop
    refine ⟨⟨Kernel.id.map Prod.snd, by kernel_sfinite⟩,
      ⟨Kernel.id.map f₁, by kernel_sfinite⟩, ?_, ?_⟩
    · cat_kernel
      rw [Kernel.id_map hf₁, Kernel.deterministic_comp_eq_map hf₁, Kernel.id_map hf₂,
        Kernel.deterministic_map hf₂ hf₁]
      ext : 1
      simp [Kernel.deterministic_apply, Kernel.id_apply, f₁]
    · cat_kernel
      rw [Kernel.id_map hf₂, Kernel.deterministic_comp_eq_map hf₂, Kernel.id_map hf₁,
        Kernel.deterministic_map hf₁ hf₂]
      ext : 1
      simp [Kernel.deterministic_apply, Kernel.id_apply, f₁]
  rightUnitor X := by
    let f₁ := fun (x : X) ↦ (x, PUnit.unit)
    have hf₁ : Measurable f₁ := by fun_prop
    have hf₂ : Measurable (Prod.fst : X × PUnit → X) := by fun_prop
    refine ⟨⟨Kernel.id.map Prod.fst, by kernel_sfinite⟩,
      ⟨Kernel.id.map f₁, by kernel_sfinite⟩, ?_, ?_⟩
    · cat_kernel
      rw [Kernel.id_map hf₁, Kernel.deterministic_comp_eq_map hf₁, Kernel.id_map hf₂,
        Kernel.deterministic_map hf₂ hf₁]
      ext : 1
      simp [Kernel.deterministic_apply, Kernel.id_apply, f₁]
    · cat_kernel
      rw [Kernel.id_map hf₂, Kernel.deterministic_comp_eq_map hf₂, Kernel.id_map hf₁,
        Kernel.deterministic_map hf₁ hf₂]
      ext : 1
      simp [Kernel.deterministic_apply, Kernel.id_apply, f₁]
  whiskerLeft_id X Y := by
    cat_kernel
    simp
  id_whiskerRight X Y := by
    cat_kernel
    simp
  id_tensorHom_id X₁ X₂ := by
    cat_kernel
    simp
  leftUnitor_naturality κ := by
    cat_kernel
    rw [Kernel.id_map (by fun_prop), Kernel.id_map (by fun_prop)]
    simp only [Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap]
    ext _ _ hs
    have := κ.2
    rw [Kernel.map_apply' _ (by fun_prop) _ hs, Kernel.comap_apply' _ (by fun_prop),
      Kernel.parallelComp_apply' <| measurable_snd hs]
    simp only [Kernel.id_apply, lintegral_dirac]
    congr
  rightUnitor_naturality κ := by
    cat_kernel
    rw [Kernel.id_map (by fun_prop), Kernel.id_map (by fun_prop)]
    simp only [Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap]
    ext _ _ hs
    have := κ.2
    rw [Kernel.map_apply' _ (by fun_prop) _ hs, Kernel.comap_apply' _ (by fun_prop),
      Kernel.parallelComp_apply' <| measurable_fst hs]
    simp only [Kernel.id_apply, MeasurableSpace.measurableSet_top, Measure.dirac_apply']
    rw [← lintegral_indicator_one hs]
    congr
  tensorHom_comp_tensorHom κ₁ κ₂ η₁ η₂ := by
    cat_kernel
    have := η₂.2
    have := η₁.2
    have := κ₁.2
    have := κ₂.2
    simp only [Kernel.comp_id_parallelComp]
    exact Kernel.parallelComp_comp_parallelComp
  associator_naturality κ₁ κ₂ η := by
    cat_kernel
    have := κ₁.2
    have := κ₂.2
    have := η.2
    simp only [Kernel.comp_id_parallelComp]
    rw [Kernel.id_map (by fun_prop), Kernel.id_map (by fun_prop),
      Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap]
    ext _ _ hs
    rw [Kernel.map_apply' _ (by fun_prop) _ hs, Kernel.comap_apply' _ (by fun_prop)]
    repeat rw [Kernel.parallelComp_apply]
    rw [Measure.prod_apply hs, Measure.prod_apply (by measurability), lintegral_prod]
    · congr with a
      rw [Measure.prod_apply (by measurability)]
      congr
    · refine Measurable.aemeasurable ?_
      exact measurable_measure_prodMk_left (by measurability)
  pentagon W X Y Z := by
    cat_kernel
    rw [Kernel.parallelComp_id_id_map (by fun_prop), Kernel.parallelComp_id_map_id (by fun_prop),
      Kernel.id_map (by fun_prop), Kernel.id_map (by fun_prop), Kernel.id_map (by fun_prop),
      Kernel.id_map (by fun_prop), Kernel.id_map (by fun_prop)]
    simp [Kernel.deterministic_comp_deterministic]
    congr 1
  triangle X Y := by
    cat_kernel
    rw [Kernel.parallelComp_id_id_map (by fun_prop), Kernel.parallelComp_id_map_id (by fun_prop),
      Kernel.id_map (by fun_prop), Kernel.id_map (by fun_prop), Kernel.id_map (by fun_prop),
      Kernel.deterministic_comp_deterministic]
    congr

instance {α : Type} [MeasurableSpace α] : IsFiniteKernel (Kernel.copy α) := by
  dsimp [Kernel.copy]
  infer_instance

/-- Every object in **Stoch** carries a canonical comonoid structure.
The comultiplication is copying `Kernel.copy X : X → X ⊗ X`
and the counit is discarding `Kernel.discard X : X → 𝟙_`. -/
instance {X : Stoch.{u}} : ComonObj X where
  counit := ⟨Kernel.Pdiscard X, by kernel_sfinite⟩
  comul := ⟨Kernel.copy X, by kernel_sfinite⟩
  counit_comul := by
    cat_kernel
    simp only [Kernel.Pdiscard, Kernel.copy]
    rw [Kernel.id_eq_deterministic_id, Kernel.deterministic_parallelComp_deterministic,
      Kernel.deterministic_comp_deterministic, Kernel.deterministic_map measurable_id (by fun_prop)]
    congr 1
  comul_counit := by
    cat_kernel
    simp only [Kernel.Pdiscard, Kernel.copy]
    rw [Kernel.id_eq_deterministic_id, Kernel.deterministic_parallelComp_deterministic,
      Kernel.deterministic_comp_deterministic, Kernel.deterministic_map measurable_id (by fun_prop)]
    congr 1
  comul_assoc := by
    cat_kernel
    rw [Kernel.id_map (by fun_prop)]
    simp [Kernel.copy, Kernel.id_eq_deterministic_id, Kernel.deterministic_comp_deterministic,
      Kernel.deterministic_parallelComp_deterministic]
    congr 1

/-- **Stoch** is a braided category with braiding given by the swap map. -/
instance : BraidedCategory Stoch.{u} where
  braiding X Y := by
    refine ⟨⟨Kernel.swap _ _, by kernel_sfinite⟩, ⟨Kernel.swap _ _, by kernel_sfinite⟩,
      ?_, ?_⟩
    · cat_kernel
      exact Kernel.swap_swap
    · cat_kernel
      exact Kernel.swap_swap
  braiding_naturality_right X Y Z κ := by
    cat_kernel
    exact Kernel.swap_parallelComp
  braiding_naturality_left κ X := by
    cat_kernel
    exact Kernel.swap_parallelComp
  hexagon_forward X Y Z := by
    cat_kernel
    repeat rw [Kernel.id_map]
    · simp only [Kernel.id_eq_deterministic_id, Kernel.swap]
      repeat rw [Kernel.deterministic_parallelComp_deterministic]
      repeat rw [Kernel.deterministic_comp_deterministic]
      congr 1
    all_goals fun_prop
  hexagon_reverse X Y Z := by
    cat_kernel
    repeat rw [Kernel.id_map]
    · simp only [Kernel.id_eq_deterministic_id, Kernel.swap]
      repeat rw [Kernel.deterministic_parallelComp_deterministic]
      repeat rw [Kernel.deterministic_comp_deterministic]
      congr 1
    all_goals fun_prop

/-- **Stoch** is a symmetric monoidal category. -/
instance : SymmetricCategory Stoch.{u} where
  symmetry X Y := by
    cat_kernel
    exact Kernel.swap_swap

/-- The comonoid on each object is commutative. -/
instance (X : Stoch.{u}) : IsCommComonObj X where
  comul_comm := by
    cat_kernel
    exact Kernel.swap_copy

end
