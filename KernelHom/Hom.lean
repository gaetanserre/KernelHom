/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import KernelHom.Mathlib.CategoryTheory.Kernel.SFinKer
import KernelHom.Mathlib.MeasurableEquiv
import Mathlib.Combinatorics.Quiver.ReflQuiver

open MeasureTheory ProbabilityTheory MeasurableEquiv

namespace ProbabilityTheory.Kernel

universe w x y

variable {X : Type x} {Y : Type y} [MeasurableSpace X] [MeasurableSpace Y]
    {X' Y' : Type w} [MeasurableSpace X'] [MeasurableSpace Y'] {ex : X' ≃ᵐ X} {ey : Y' ≃ᵐ Y}

section Hom

noncomputable
def fromHom (κ : SFinKer.of X' ⟶ SFinKer.of Y') : Kernel X Y :=
  (κ.1.comap ex.symm (by fun_prop)).map ey

instance {κ : SFinKer.of X' ⟶ SFinKer.of Y'} :
    IsSFiniteKernel (fromHom (ex := ex) (ey := ey) κ) := by
  simp only [fromHom]
  have := κ.2
  infer_instance

noncomputable
def hom (κ : Kernel X Y) [IsSFiniteKernel κ] : SFinKer.of X' ⟶ SFinKer.of Y' := by
  refine ⟨(κ.map ey.symm).comap ex (by fun_prop), ?_⟩
  have := κ.2
  infer_instance

noncomputable
def hom' (κ : Kernel X Y) [IsSFiniteKernel κ] :
    SFinKer.of (ULift.{max w y} X) ⟶ SFinKer.of (ULift.{max w x} Y) :=
  hom (ex := ulift) (ey := ulift) κ

lemma quiver_congr {κ₁ κ₂ : Kernel X Y} [IsSFiniteKernel κ₁] [IsSFiniteKernel κ₂] :
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
  · rintro rfl
    rfl

section Comp

universe z

variable {Z : Type z} [MeasurableSpace Z] {Z' : Type w} [MeasurableSpace Z'] {ez : Z' ≃ᵐ Z}

open CategoryTheory

lemma quiver_comp {κ₁ : Kernel X Y} {κ₂ : Kernel Z X} [IsSFiniteKernel κ₁] [IsSFiniteKernel κ₂] :
    hom (ex := ez) (ey := ex) κ₂ ≫ hom (ex := ex) (ey := ey) κ₁
      = hom (ex := ez) (ey := ey) (κ₁ ∘ₖ κ₂) := by
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

lemma quiver_id : 𝟙 (SFinKer.of X') = hom (ex := ex) (ey := ex) Kernel.id := by
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

lemma leftUnitor : (λ_ (SFinKer.of X')).hom = hom (ex := punit.prod ex) (ey := ex)
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

lemma rightUnitor : (ρ_ (SFinKer.of X')).hom = hom (ex := ex.prod punit) (ey := ex)
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

end unitors

section whiskers

variable {Z : Type z} [MeasurableSpace Z] {Z' : Type w} [MeasurableSpace Z'] {ez : Z' ≃ᵐ Z}

lemma WhiskerLeft {κ : Kernel X Y} [IsSFiniteKernel κ] :
    SFinKer.of Z' ◁ κ.hom (ex := ex) (ey := ey) =
      hom (ex := ez.prod ex) (ey := ez.prod ey) ((Kernel.id (α := Z)) ∥ₖ κ) := by
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
      hom (ex := ex.prod ez) (ey := ey.prod ez) (κ ∥ₖ Kernel.id (α := Z)) := by
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

end ProbabilityTheory.Kernel
