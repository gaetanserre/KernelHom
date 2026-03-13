/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import LeanStoch.Stoch
import Mathlib.Combinatorics.Quiver.ReflQuiver

open MeasureTheory ProbabilityTheory MeasurableEquiv

namespace ProbabilityTheory.Kernel

universe w x y

variable {X : Type x} {Y : Type y} [MeasurableSpace X] [MeasurableSpace Y]
    {X' Y' : Type w} [MeasurableSpace X'] [MeasurableSpace Y'] {ex : X' ≃ᵐ X} {ey : Y' ≃ᵐ Y}


noncomputable
def fromQuiver (κ : Stoch.of X' ⟶ Stoch.of Y') : Kernel X Y :=
  (κ.1.comap ex.symm (by fun_prop)).map ey

instance {κ : Stoch.of X' ⟶ Stoch.of Y'} :
    IsSFiniteKernel (fromQuiver (ex := ex) (ey := ey) κ) := by
  simp only [fromQuiver]
  kernel_sfinite

noncomputable
def quiver (κ : Kernel X Y) [IsSFiniteKernel κ] : Stoch.of X' ⟶ Stoch.of Y' := by
  refine ⟨(κ.map ey.symm).comap ex (by fun_prop), ?_⟩
  kernel_sfinite

noncomputable
def quiver' (κ : Kernel X Y) [IsSFiniteKernel κ] :
    Stoch.of (ULift.{max w y} X) ⟶ Stoch.of (ULift.{max w x} Y) :=
  quiver (ex := ulift) (ey := ulift) κ

-- Lemmas for compatibility between kernel operations and quiver morphisms

@[simp]
lemma quiver_congr {κ₁ κ₂ : Kernel X Y} [IsSFiniteKernel κ₁] [IsSFiniteKernel κ₂] :
    κ₁ = κ₂ ↔ quiver (ex := ex) (ey := ey) κ₁ = quiver (ex := ex) (ey := ey) κ₂ := by
  constructor
  · rintro rfl
    rfl
  · intro h
    rw [Subtype.ext_iff] at h
    ext x s hs
    replace h := DFunLike.congr (x := ex.symm x) h rfl
    simp only [quiver, coe_comap, Function.comp_apply, apply_symm_apply] at h
    rw [Kernel.map_apply, Kernel.map_apply] at h
    · replace h := DFunLike.congr (x := ey.symm '' s) h rfl
      rw [Measure.map_apply, Measure.map_apply] at h
      · simpa using h
      all_goals try fun_prop
      all_goals measurability
    all_goals fun_prop

section

universe z

variable {Z : Type z} [MeasurableSpace Z] {Z' : Type w} [MeasurableSpace Z'] {ez : Z' ≃ᵐ Z}

open CategoryTheory

@[simp]
lemma quiver_comp {κ₁ : Kernel X Y} {κ₂ : Kernel Z X} [IsSFiniteKernel κ₁] [IsSFiniteKernel κ₂] :
    quiver (ex := ez) (ey := ey) (κ₁ ∘ₖ κ₂) =
      quiver (ex := ez) (ey := ex) κ₂ ≫ quiver (ex := ex) (ey := ey) κ₁ := by
  cat_kernel
  simp only [quiver]
  ext x s hs
  rw [Kernel.map_comp, ← Kernel.comp_map, Kernel.comap_apply, Kernel.comp_apply',
    Kernel.comp_apply', Kernel.map_apply, Kernel.comap_apply, Kernel.map_apply,
  ]
  · simp
  all_goals try fun_prop
  all_goals measurability

end

end ProbabilityTheory.Kernel
