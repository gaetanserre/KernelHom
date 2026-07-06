/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import KernelLift.ForMathlib.MeasurableEquiv
public import KernelLift.ForMathlib.Kernel
public import Mathlib

/-!
# Kernel morphisms

This file defines the transformation between categorical morphisms in `SFinKer` and kernel objects.

## Main declarations

* `fromHom`: transforms a categorical morphism in `SFinKer` to a `Kernel`.
* `hom`: transforms a `Kernel` to a categorical morphism in `SFinKer`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MeasurableEquiv
open scoped SFinKer CategoryTheory CategoryTheory.MonoidalCategory

namespace ProbabilityTheory.Kernel

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {SX SY : SFinKer} {ex : SX ≃ᵐ X} {ey : SY ≃ᵐ Y}

/-- Transform a kernel into a morphism in `SFinKer`. -/
noncomputable def hom (κ : Kernel X Y) [IsSFiniteKernel κ] : SX ⟶ SY := by
  refine ⟨(κ.map ey.symm).comap ex (by fun_prop), ?_⟩
  have := κ.2
  infer_instance

lemma hom_apply (κ : Kernel X Y) [IsSFiniteKernel κ] (a : SX) :
    (κ.hom (ex := ex) (ey := ey)).1 a = (κ.map ey.symm) (ex a) := rfl

lemma hom_apply' (κ : Kernel X Y) [IsSFiniteKernel κ] (a : SX) {s : Set SY}
    (hs : MeasurableSet s) :
    (κ.hom (ex := ex) (ey := ey)).1 a s = κ (ex a) (ey '' s) := by
  simp only [hom, coe_comap, Function.comp_apply]
  rw [map_apply' _ ey.symm.measurable _ hs, preimage_symm]

lemma hom_congr {κ η : Kernel X Y} [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    κ.hom (ex := ex) (ey := ey) = η.hom (ex := ex) (ey := ey) ↔ κ = η := by
  constructor
  · intro h
    ext a s hs
    replace h := DFunLike.congr (x := ex.symm a) (congrArg SFinKer.Hom.hom h) rfl
    replace h := DFunLike.congr (x := ey.symm '' s) h rfl
    rw [hom_apply', hom_apply'] at h
    · simp only [apply_symm_apply] at h
      rwa [image_symm, image_preimage] at h
    · measurability
    · measurability
  · grind

variable {T Z : Type*} [MeasurableSpace T] [MeasurableSpace Z]
    {ST SZ : SFinKer} {et : ST ≃ᵐ T} {ez : SZ ≃ᵐ Z}

lemma comp_hom (η : Kernel X Y) (κ : Kernel Z X) [IsSFiniteKernel η] [IsSFiniteKernel κ] :
    κ.hom (ex := ez) (ey := ex) ≫ η.hom (ex := ex) (ey := ey) =
      (η ∘ₖ κ).hom (ex := ez) (ey := ey) := by
  ext a s hs
  dsimp
  rw [hom_apply', comp_apply', comp_apply', hom_apply, lintegral_map]
  · congr with y
    simp [hom_apply' _ _ hs]
  all_goals try fun_prop
  all_goals try measurability
  · exact Kernel.measurable_coe η.hom.hom hs

lemma parallelComp_hom (κ : Kernel X Y) (η : Kernel Z T) [IsSFiniteKernel η] [IsSFiniteKernel κ] :
    κ.hom (ex := ex) (ey := ey) ⊗ₘ η.hom (ex := ez) (ey := et) =
      hom (ex := ex.prod ez) (ey := ey.prod et) (κ ∥ₖ η) := by
  ext : 1; dsimp
  simp only [hom]
  rw [id_parallelComp_comp_parallelComp_id, comap_parallelComp_comap, map_parallelComp_map]
  · rfl
  all_goals fun_prop

lemma id_hom : 𝟙 SX = Kernel.id.hom (ex := ex) (ey := ex) := by
  ext; dsimp
  rw [hom_apply', id_apply, id_apply, Measure.dirac_apply', Measure.dirac_apply']
  · exact Set.indicator_eq_indicator (by simp) rfl
  all_goals measurability

lemma leftUnitor_hom : (λ_ SX).hom = hom (ex := punit.prod ex) (ey := ex)
    (Kernel.id.map (Prod.snd : PUnit × X → X)) := by
  ext; dsimp
  rw [hom_apply', id_map (by fun_prop), id_map (by fun_prop), deterministic_apply',
    deterministic_apply']
  · refine Set.indicator_eq_indicator ?_ rfl
    simp [MeasurableEquiv.prod]
  all_goals measurability

lemma leftUnitor_inv : (λ_ SX).inv = hom (ex := ex) (ey := punit.prod ex)
    (Kernel.id.map (fun x ↦ (PUnit.unit, x))) := by
  ext; dsimp
  rw [hom_apply', id_map (by fun_prop), id_map (by fun_prop), deterministic_apply',
    deterministic_apply', Set.image]
  · refine Set.indicator_eq_indicator ?_ rfl
    simp only [SFinKer.tensorObj_carrier, SFinKer.tensorUnit_carrier, MeasurableEquiv.prod,
      MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, Prod.exists, Set.mem_setOf_eq, Prod.mk.injEq,
      EmbeddingLike.apply_eq_iff_eq, true_and, exists_eq_right]
    exact ⟨fun ha => ⟨_, ha⟩, fun ⟨a, ha⟩ => by simp_all⟩
  all_goals measurability

lemma rightUnitor_hom : (ρ_ SX).hom = hom (ex := ex.prod punit) (ey := ex)
    (Kernel.id.map (Prod.fst : X × PUnit → X)) := by
  ext; dsimp
  rw [hom_apply', id_map (by fun_prop), id_map (by fun_prop), deterministic_apply',
    deterministic_apply']
  · refine Set.indicator_eq_indicator ?_ rfl
    simp [MeasurableEquiv.prod]
  all_goals measurability

lemma rightUnitor_inv : (ρ_ SX).inv = hom (ex := ex) (ey := ex.prod punit)
    (Kernel.id.map (fun x ↦ (x, PUnit.unit))) := by
  ext; dsimp
  rw [hom_apply', id_map (by fun_prop), id_map (by fun_prop), deterministic_apply',
    deterministic_apply']
  · refine Set.indicator_eq_indicator ?_ rfl
    simp only [SFinKer.tensorObj_carrier, SFinKer.tensorUnit_carrier, MeasurableEquiv.prod,
      MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, Set.mem_image, Prod.mk.injEq,
      EmbeddingLike.apply_eq_iff_eq, and_true, Prod.exists, exists_and_right, exists_eq_right]
    exact ⟨fun ha => ⟨_, ha⟩, fun ⟨a, ha⟩ => by simp_all⟩
  all_goals measurability

lemma associator_hom : (α_ SX SY SZ).hom =
    hom (ex := (ex.prod ey).prod ez) (ey := ex.prod (ey.prod ez))
      (Kernel.deterministic prodAssoc (by fun_prop)) := by
  ext : 1; dsimp
  simp only [hom]
  rw [deterministic_map (by fun_prop) (by fun_prop)]
  congr with x
  all_goals simp [MeasurableEquiv.prod, prodAssoc]

lemma associator_inv : (α_ SX SY SZ).inv =
    hom (ex := ex.prod (ey.prod ez)) (ey := (ex.prod ey).prod ez)
      (Kernel.deterministic prodAssoc.symm (by fun_prop)) := by
  ext : 1; dsimp
  simp only [hom]
  rw [deterministic_map (by fun_prop) (by fun_prop)]
  congr with x
  all_goals simp [MeasurableEquiv.prod, prodAssoc]

end ProbabilityTheory.Kernel
