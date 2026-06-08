/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib

/-!
# Kernel morphisms

This file defines the transformation between categorical morphisms in `SFinKer` and kernel objects.

## Main declarations

* `fromHom`: transforms a categorical morphism in `SFinKer` to a `Kernel`.
* `hom`: transforms a `Kernel` to a categorical morphism in `SFinKer`.
-/

@[expose] public section

open ProbabilityTheory MeasurableEquiv
open scoped SFinKer

namespace ProbabilityTheory.Kernel

variable {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y]
    {SX SY : SFinKer.{u}} {ex : SX ≃ᵐ X} {ey : SY ≃ᵐ Y}

/-- Transform a kernel into a morphism in `SFinKer`. -/
noncomputable def hom (κ : Kernel X Y) [IsSFiniteKernel κ] : SX ⟶ SY := by
  refine ⟨(κ.map ey.symm).comap ex (by fun_prop), ?_⟩
  have := κ.2
  infer_instance

lemma hom_apply (κ : Kernel X Y) [IsSFiniteKernel κ] (a : SX) :
    (hom (ex := ex) (ey := ey) κ).1 a = (κ.map ey.symm) (ex a) := rfl

lemma hom_apply' (κ : Kernel X Y) [IsSFiniteKernel κ] (a : SX) {s : Set SY}
    (hs : MeasurableSet s) :
    (hom (ex := ex) (ey := ey) κ).1 a s = κ (ex a) (ey '' s) := by
  simp only [hom, coe_comap, Function.comp_apply]
  rw [map_apply' _ ey.symm.measurable _ hs, preimage_symm]

lemma hom_congr {κ η : Kernel X Y} [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    hom (ex := ex) (ey := ey) κ = hom (ex := ex) (ey := ey) η ↔ κ = η := by
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

end ProbabilityTheory.Kernel
