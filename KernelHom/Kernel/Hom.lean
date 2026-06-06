/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import KernelHom.Mathlib.MeasurableEquiv
public import KernelHom.Mathlib.Kernel
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Probability.Kernel.Category.SFinKer
public import Mathlib.CategoryTheory.CopyDiscardCategory.Deterministic

/-!
# Kernel morphisms

This file defines the transformation between categorical morphisms in `SFinKer` and kernel objects.

## Main declarations

* `fromHom`: transforms a categorical morphism in `SFinKer` to a `Kernel`.
* `hom`: transforms a `Kernel` to a categorical morphism in `SFinKer`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MeasurableEquiv

open scoped SFinKer

namespace ProbabilityTheory.Kernel

universe w x y z

variable {X : Type x} {Y : Type y} [MeasurableSpace X] [MeasurableSpace Y]
    {X' Y' : SFinKer.{w}} {ex : X'.carrier ≃ᵐ X} {ey : Y'.carrier ≃ᵐ Y}

section Hom

/-- Transform a morphism in `SFinKer` into a kernel. -/
noncomputable def fromHom (κ : X' ⟶ Y') : Kernel X Y := (κ.1.comap ex.symm (by fun_prop)).map ey

instance {κ : SFinKer.of X' ⟶ SFinKer.of Y'} :
    IsSFiniteKernel (fromHom (ex := ex) (ey := ey) κ) := by
  simp only [fromHom]
  have := κ.2
  infer_instance

/-- Transform a kernel into a morphism in `SFinKer`. -/
noncomputable def hom (κ : Kernel X Y) [IsSFiniteKernel κ] : X' ⟶ Y' := by
  refine ⟨(κ.map ey.symm).comap ex (by fun_prop), ?_⟩
  have := κ.2
  infer_instance

lemma hom_congr {κ₁ κ₂ : Kernel X Y} [IsSFiniteKernel κ₁] [IsSFiniteKernel κ₂] :
    hom (ex := ex) (ey := ey) κ₁ = hom (ex := ex) (ey := ey) κ₂ ↔ κ₁ = κ₂ := by
  constructor
  · intro h
    ext a s hs
    replace h := DFunLike.congr (x := ex.symm a) (congrArg SFinKer.Hom.hom h) rfl
    simp only [hom, coe_comap, Function.comp_apply, apply_symm_apply] at h
    rw [map_apply, map_apply] at h
    · replace h := DFunLike.congr (x := ey.symm '' s) h rfl
      rw [Measure.map_apply, Measure.map_apply] at h
      · simpa using h
      all_goals try fun_prop
      all_goals measurability
    all_goals fun_prop
  · grind

section Comp

variable {Z : Type z} [MeasurableSpace Z] {Z' : SFinKer.{w}} {ez : Z'.carrier ≃ᵐ Z}

open CategoryTheory

lemma hom_comp {κ : Kernel X Y} {η : Kernel Z X} [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    η.hom (ex := ez) (ey := ex) ≫ κ.hom (ex := ex) (ey := ey)
      = (κ ∘ₖ η).hom (ex := ez) (ey := ey) := by
  ext; dsimp
  simp only [hom]
  rw [map_comp, ← comp_map, comap_apply, comp_apply', comp_apply', map_apply, comap_apply,
    map_apply]
  · simp
  all_goals try fun_prop
  all_goals measurability

end Comp

end Hom

open CategoryTheory MonoidalCategory

section id

lemma hom_id : 𝟙 (SFinKer.of X') = hom (ex := ex) (ey := ex) Kernel.id := by
  ext; dsimp
  simp only [hom]
  rw [Kernel.id_map, Kernel.comap_apply', Kernel.deterministic_apply', Kernel.id_apply,
    Measure.dirac_apply']
  · congr
    simp
  all_goals try fun_prop
  all_goals measurability

end id

section unitors

lemma leftUnitor_hom : (λ_ (SFinKer.of X')).hom = hom (ex := punit.prod ex) (ey := ex)
    (Kernel.id.map (Prod.snd : PUnit × X → X)) := by
  ext _ _ hs; dsimp
  simp only [hom]
  rw [map_apply', comap_apply', map_apply', map_apply', id_apply, id_apply]
  · simp only [Set.preimage, Set.mem_setOf_eq]
    rw [Measure.dirac_apply', Measure.dirac_apply']
    · refine Set.indicator_eq_indicator (Iff.intro (fun h ↦ ?_) (fun h ↦ ?_)) rfl
      · simpa [punit, MeasurableEquiv.prod]
      · simpa [punit, MeasurableEquiv.prod] using h
    · rw [measurableSet_setOf]
      exact Measurable.comp hs.mem <| .comp ex.symm.measurable measurable_snd
    · rw [measurableSet_setOf]
      exact Measurable.comp hs.mem measurable_snd
  all_goals try fun_prop
  all_goals measurability

lemma leftUnitor_inv : (λ_ (SFinKer.of X')).inv = hom (ex := ex) (ey := punit.prod ex)
    (Kernel.id.map (fun x ↦ (PUnit.unit, x))) := by
  ext _ _ hs; dsimp
  simp only [hom]
  rw [map_apply', comap_apply', map_apply', map_apply', id_apply, id_apply]
  · simp only [Set.preimage, Set.mem_setOf_eq]
    rw [Measure.dirac_apply', Measure.dirac_apply']
    · refine Set.indicator_eq_indicator (Iff.intro (fun h ↦ ?_) (fun h ↦ ?_)) rfl
      · simpa [punit, MeasurableEquiv.prod]
      · simpa [punit, MeasurableEquiv.prod] using h
    · rw [measurableSet_setOf]
      exact Measurable.comp hs.mem <| .comp (punit.prod ex).symm.measurable measurable_prodMk_left
    · rw [measurableSet_setOf]
      exact Measurable.comp hs.mem measurable_prodMk_left
  all_goals try fun_prop
  all_goals measurability

lemma rightUnitor_hom : (ρ_ (SFinKer.of X')).hom = hom (ex := ex.prod punit) (ey := ex)
    (Kernel.id.map (Prod.fst : X × PUnit → X)) := by
  ext _ _ hs; dsimp
  simp only [hom]
  rw [map_apply', comap_apply', map_apply', map_apply', id_apply, id_apply]
  · simp only [Set.preimage, Set.mem_setOf_eq]
    rw [Measure.dirac_apply', Measure.dirac_apply']
    · refine Set.indicator_eq_indicator (Iff.intro (fun h ↦ ?_) (fun h ↦ ?_)) rfl
      · simpa [punit, MeasurableEquiv.prod]
      · simpa [punit, MeasurableEquiv.prod] using h
    · rw [measurableSet_setOf]
      exact Measurable.comp hs.mem <| .comp ex.symm.measurable measurable_fst
    · rw [measurableSet_setOf]
      exact Measurable.comp hs.mem measurable_fst
  all_goals try fun_prop
  all_goals measurability

lemma rightUnitor_inv : (ρ_ (SFinKer.of X')).inv = hom (ex := ex) (ey := ex.prod punit)
    (Kernel.id.map (fun x ↦ (x, PUnit.unit))) := by
  ext _ _ hs; dsimp
  simp only [hom]
  rw [map_apply', comap_apply', map_apply', map_apply', id_apply, id_apply]
  · simp only [Set.preimage, Set.mem_setOf_eq]
    rw [Measure.dirac_apply', Measure.dirac_apply']
    · refine Set.indicator_eq_indicator (Iff.intro (fun h ↦ ?_) (fun h ↦ ?_)) rfl
      · simpa [punit, MeasurableEquiv.prod]
      · simpa [punit, MeasurableEquiv.prod] using h
    · rw [measurableSet_setOf]
      exact Measurable.comp hs.mem <| .comp (ex.prod punit).symm.measurable measurable_prodMk_right
    · rw [measurableSet_setOf]
      exact Measurable.comp hs.mem measurable_prodMk_right
  all_goals try fun_prop
  all_goals measurability

end unitors

variable {Z : Type z} [MeasurableSpace Z] {Z' : SFinKer.{w}} {ez : Z'.carrier ≃ᵐ Z}

section whiskers

lemma WhiskerLeft {κ : Kernel X Y} [IsSFiniteKernel κ] :
    SFinKer.of Z' ◁ κ.hom (ex := ex) (ey := ey) =
      ((Kernel.id (α := Z)) ∥ₖ κ).hom (ex := ez.prod ex) (ey := ez.prod ey) := by
  ext _ _ hs; dsimp
  simp only [hom]
  rw [parallelComp_apply, comap_apply, map_apply, id_apply,
    comap_apply, map_apply, parallelComp_apply, id_apply]
  · simp only [Measure.dirac_prod, MeasurableEquiv.prod]
    rw [Measure.map_map, Measure.map_map, Measure.map_apply, Measure.map_apply]
    · congr with y
      · simp
      · simp
    all_goals try fun_prop
    all_goals exact hs
  all_goals fun_prop

lemma WhiskerRight {κ : Kernel X Y} [IsSFiniteKernel κ] :
    κ.hom (ex := ex) (ey := ey) ▷ SFinKer.of Z' =
      (κ ∥ₖ Kernel.id (α := Z)).hom (ex := ex.prod ez) (ey := ey.prod ez) := by
  ext _ _ hs; dsimp
  simp only [hom]
  rw [parallelComp_apply, comap_apply, map_apply, id_apply,
    comap_apply, map_apply, parallelComp_apply, id_apply]
  · simp only [Measure.prod_dirac, MeasurableEquiv.prod]
    rw [Measure.map_map, Measure.map_map, Measure.map_apply, Measure.map_apply]
    · congr with y
      · simp
      · simp
    all_goals try fun_prop
    all_goals exact hs
  all_goals fun_prop

end whiskers

section associator

lemma associator_hom : (α_ (SFinKer.of X') (SFinKer.of Y') (SFinKer.of Z')).hom =
    hom (ex := (ex.prod ey).prod ez) (ey := ex.prod (ey.prod ez))
      (Kernel.deterministic prodAssoc (by fun_prop)) := by
  ext : 1; dsimp
  simp only [hom]
  rw [deterministic_map (by fun_prop) (by fun_prop)]
  congr with x
  all_goals simp [MeasurableEquiv.prod, prodAssoc]

lemma associator_inv : (α_ (SFinKer.of X') (SFinKer.of Y') (SFinKer.of Z')).inv =
    hom (ex := ex.prod (ey.prod ez)) (ey := (ex.prod ey).prod ez)
      (Kernel.deterministic prodAssoc.symm (by fun_prop)) := by
  ext : 1; dsimp
  simp only [hom]
  rw [deterministic_map (by fun_prop) (by fun_prop)]
  congr with x
  all_goals simp [MeasurableEquiv.prod, prodAssoc]

end associator

section tensorHom

variable {V : Type v} [MeasurableSpace V] {V' : SFinKer.{w}} {ev : V'.carrier ≃ᵐ V}

lemma tensorHom {κ : Kernel X Y} [IsSFiniteKernel κ] {η : Kernel V Z} [IsSFiniteKernel η] :
    κ.hom (ex := ex) (ey := ey) ⊗ₘ η.hom (ex := ev) (ey := ez) =
      (κ ∥ₖ η).hom (ex := ex.prod ev) (ey := ey.prod ez) := by
  ext : 1; dsimp
  simp only [hom]
  rw [id_parallelComp_comp_parallelComp_id, comap_parallelComp_comap, map_parallelComp_map]
  · congr
  all_goals fun_prop

end tensorHom

section braiding

lemma braiding_hom : (β_ (SFinKer.of X') (SFinKer.of Y')).hom =
    (Kernel.swap X Y).hom (ex := ex.prod ey) (ey := ey.prod ex) := by
  ext : 1; dsimp
  simp only [hom]
  ext a s hs
  rw [swap_apply, comap_apply, map_apply, swap_apply, Measure.map_apply, Measure.dirac_apply',
    Measure.dirac_apply']
  · simp only [Prod.swap, Set.preimage, MeasurableEquiv.prod, symm_mk, MeasurableEquiv.coe_mk,
    Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk]
    exact Set.indicator_eq_indicator (by simp) rfl
  all_goals try fun_prop
  all_goals measurability

end braiding

section comonobj

open scoped ComonObj

lemma counit : ε[SFinKer.of X'] = (Kernel.discard X).hom (ex := ex) (ey := punit) := by
  ext : 1; dsimp
  simp only [hom]
  ext : 1
  rw [discard_apply, comap_apply, map_apply]
  · simp
  · fun_prop

lemma comul : Δ[SFinKer.of X'] = (Kernel.copy X).hom (ex := ex) (ey := ex.prod ex) := by
  ext : 1; dsimp
  simp only [hom]
  ext : 1
  rw [copy_apply, comap_apply, map_apply, copy_apply, Measure.map_dirac']
  · congr
    all_goals simp
  all_goals fun_prop

end comonobj

section deterministic

instance {κ : Kernel X Y} [IsMarkovKernel κ] [IsDeterministic κ] :
    Deterministic (hom (ex := ex) (ey := ey) κ) where
  hom_counit := by
    ext : 1; dsimp
    simp only [hom]
    have : IsMarkovKernel ((κ.map ey.symm).comap ex (by fun_prop)) :=
      have : IsMarkovKernel (κ.map ey.symm) :=
        IsMarkovKernel.map _ (by fun_prop)
      IsMarkovKernel.comap _ (by fun_prop)
    exact Kernel.comp_discard _
  hom_comul := by
    ext : 1; dsimp
    simp only [hom]
    rw [id_parallelComp_comp_parallelComp_id, comap_parallelComp_comap, map_parallelComp_map]
    · ext a s hs
      have := (κ.parallelComp_self_comp_copy).symm
      replace this := DFunLike.congr_fun this <| ex a
      replace this := DFunLike.congr_fun this (ey.prod ey '' s)
      rw [comp_apply, comp_apply] at this ⊢
      rw [comap_apply, map_apply, copy_apply]
      · rw [Measure.bind_apply, Measure.bind_apply] at this ⊢
        · rw [MeasureTheory.lintegral_map, lintegral_dirac', comap_apply, map_apply',
          parallelComp_apply']
          · convert this using 1
            · congr with y
              simp only [copy_apply]
              rw [Measure.dirac_apply', Measure.dirac_apply']
              · refine Set.indicator_eq_indicator ?_ rfl
                simp [MeasurableEquiv.prod]
                aesop
              all_goals try measurability
            · rw [copy_apply, lintegral_dirac', parallelComp_apply']
              · congr with y
                simp
                congr 2
                simp [MeasurableEquiv.prod, Set.image, Set.preimage]
                aesop
              all_goals try measurability
              exact Kernel.measurable_coe _ (by measurability)
          all_goals try fun_prop
          all_goals try measurability
          all_goals exact Kernel.measurable_coe _ hs
        all_goals try fun_prop
        all_goals try measurability
      all_goals try fun_prop
    all_goals try fun_prop

end deterministic

end ProbabilityTheory.Kernel
