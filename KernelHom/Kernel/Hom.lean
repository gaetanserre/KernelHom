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
    (hom (ex := ex) (ey := ey) κ) ⊗ₘ (hom (ex := ez) (ey := et) η) =
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

end ProbabilityTheory.Kernel
