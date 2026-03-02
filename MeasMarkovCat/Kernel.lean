import Mathlib
import MeasMarkovCat.Tactics
import MeasMarkovCat.Mathlib.Kernel

open CategoryTheory ProbabilityTheory MeasureTheory

universe u

structure MeasCatKer : Type (u + 1) where
  of ::
  carrier : Type u
  [str : MeasurableSpace carrier]

attribute [instance] MeasCatKer.str

instance : CoeSort MeasCatKer Type* :=
  ⟨MeasCatKer.carrier⟩

noncomputable section

instance : LargeCategory MeasCatKer where
  Hom X Y := { k : Kernel X Y // IsSFiniteKernel k }
  id X := ⟨Kernel.id, by kernel_sfiniteness⟩
  comp κ₁ κ₂ := ⟨κ₂.1 ∘ₖ κ₁.1, by kernel_sfiniteness⟩
  assoc κ₁ κ₂ κ₃ := by simp [Kernel.comp_assoc]

instance : MonoidalCategory MeasCatKer where
  tensorObj X Y := MeasCatKer.of (X × Y)
  whiskerLeft X Y₁ Y₂ κ := ⟨Kernel.id ∥ₖ κ.1, by kernel_sfiniteness⟩
  whiskerRight κ Y := ⟨κ.1 ∥ₖ Kernel.id, by kernel_sfiniteness⟩
  tensorUnit := MeasCatKer.of Unit
  associator X Y Z := by
    let f₁ := fun (x : (X × Y) × Z) ↦ (x.1.1, x.1.2, x.2)
    let f₂ := fun (x : X × Y × Z) ↦ ((x.1, x.2.1), x.2.2)
    have hf₁ : Measurable f₁ := by fun_prop
    have hf₂ : Measurable f₂ := by fun_prop
    refine ⟨⟨Kernel.id.map f₁, by kernel_sfiniteness⟩,
      ⟨Kernel.id.map f₂, by kernel_sfiniteness⟩, ?_, ?_⟩
    · cat_kernel
      rw [Kernel.id_map hf₁, Kernel.id_map hf₂, Kernel.deterministic_comp_eq_map hf₂,
        Kernel.deterministic_map hf₁ hf₂]
      ext x s hs
      simp [Kernel.deterministic_apply, Kernel.id_apply, f₁, f₂]
    · cat_kernel
      rw [Kernel.id_map hf₂, Kernel.id_map hf₁, Kernel.deterministic_comp_eq_map hf₁,
        Kernel.deterministic_map hf₂ hf₁]
      ext x s hs
      simp [Kernel.deterministic_apply, Kernel.id_apply, f₁, f₂]
  leftUnitor X := by
    let f₁ := fun (x : X) ↦ ((), x)
    have hf₁ : Measurable f₁ := by fun_prop
    have hf₂ : Measurable (Prod.snd : Unit × X → X) := by fun_prop
    refine ⟨⟨Kernel.id.map Prod.snd, by kernel_sfiniteness⟩,
      ⟨Kernel.id.map f₁, by kernel_sfiniteness⟩, ?_, ?_⟩
    · cat_kernel
      rw [Kernel.id_map hf₁, Kernel.deterministic_comp_eq_map hf₁, Kernel.id_map hf₂,
        Kernel.deterministic_map hf₂ hf₁]
      ext x s hs
      simp [Kernel.deterministic_apply, Kernel.id_apply, f₁]
    · cat_kernel
      rw [Kernel.id_map hf₂, Kernel.deterministic_comp_eq_map hf₂, Kernel.id_map hf₁,
        Kernel.deterministic_map hf₁ hf₂]
      ext x s hs
      simp [Kernel.deterministic_apply, Kernel.id_apply, f₁]
  rightUnitor X := by
    let f₁ := fun (x : X) ↦ (x, ())
    have hf₁ : Measurable f₁ := by fun_prop
    have hf₂ : Measurable (Prod.fst : X × Unit → X) := by fun_prop
    refine ⟨⟨Kernel.id.map Prod.fst, by kernel_sfiniteness⟩,
      ⟨Kernel.id.map f₁, by kernel_sfiniteness⟩, ?_, ?_⟩
    · cat_kernel
      rw [Kernel.id_map hf₁, Kernel.deterministic_comp_eq_map hf₁, Kernel.id_map hf₂,
        Kernel.deterministic_map hf₂ hf₁]
      ext x s hs
      simp [Kernel.deterministic_apply, Kernel.id_apply, f₁]
    · cat_kernel
      rw [Kernel.id_map hf₂, Kernel.deterministic_comp_eq_map hf₂, Kernel.id_map hf₁,
        Kernel.deterministic_map hf₁ hf₂]
      ext x s hs
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
    ext x s hs
    have : IsSFiniteKernel κ.1 := κ.2
    rw [Kernel.map_apply' _ (by fun_prop) _ hs, Kernel.comap_apply' _ (by fun_prop),
      Kernel.parallelComp_apply' <| measurable_snd hs]
    simp only [Kernel.id_apply, lintegral_dirac]
    congr
  rightUnitor_naturality κ := by
    cat_kernel
    rw [Kernel.id_map (by fun_prop), Kernel.id_map (by fun_prop)]
    simp only [Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap]
    ext x s hs
    have : IsSFiniteKernel κ.1 := κ.2
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
    ext x s hs
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

-- Use `ProbabilityTheory.Kernel.copy` in the `ComonObj` instance.

end
