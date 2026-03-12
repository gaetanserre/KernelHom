/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import LeanStoch.Stoch
import Mathlib.Combinatorics.Quiver.ReflQuiver

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.Kernel

universe w x y

variable {X : Type x} {Y : Type y} [MeasurableSpace X] [MeasurableSpace Y]

noncomputable
def fromQuiver (κ : Stoch.of (ULift.{max w y} X) ⟶ Stoch.of (ULift.{max w x} Y)) : Kernel X Y :=
  (κ.1.comap MeasurableEquiv.ulift.symm (by fun_prop)).map MeasurableEquiv.ulift

instance {κ : Stoch.of (ULift.{max w y} X) ⟶ Stoch.of (ULift.{max w x} Y)} :
    IsSFiniteKernel (fromQuiver κ) := by
  simp only [fromQuiver]
  kernel_sfinite

noncomputable
def toQuiver (κ : Kernel X Y) [IsSFiniteKernel κ] :
    Stoch.of (ULift.{max w y} X) ⟶ Stoch.of (ULift.{max w x} Y) := by
  refine ⟨(κ.map MeasurableEquiv.ulift.symm).comap MeasurableEquiv.ulift (by fun_prop), ?_⟩
  kernel_sfinite

-- Lemmas for compatibility between kernel operations and quiver morphisms

@[simp]
lemma toQuiver_congr {κ₁ κ₂ : Kernel X Y} [IsSFiniteKernel κ₁] [IsSFiniteKernel κ₂] :
    κ₁ = κ₂ ↔ toQuiver.{w} κ₁ = toQuiver κ₂ := by
  constructor
  · rintro rfl
    rfl
  · intro h
    rw [Subtype.ext_iff] at h
    ext x s hs
    replace h := DFunLike.congr (x := MeasurableEquiv.ulift.symm x) h rfl
    simp only [toQuiver, coe_comap, Function.comp_apply, MeasurableEquiv.apply_symm_apply] at h
    rw [Kernel.map_apply, Kernel.map_apply] at h
    · replace h := DFunLike.congr (x := MeasurableEquiv.ulift.symm '' s) h rfl
      rw [Measure.map_apply, Measure.map_apply] at h
      · simpa using h
      all_goals try fun_prop
      all_goals measurability
    all_goals fun_prop

section

universe z

variable {Z : Type z} [MeasurableSpace Z]

open CategoryTheory

@[simp]
lemma toQuiver_comp {κ₁ : Kernel X Y} {κ₂ : Kernel Z X} [IsSFiniteKernel κ₁] [IsSFiniteKernel κ₂] :
    toQuiver.{max w x y z} (κ₁ ∘ₖ κ₂) = toQuiver.{max w x y z} κ₂ ≫ toQuiver.{max w x y z} κ₁ := by
  cat_kernel
  simp only [toQuiver]
  ext x s hs
  rw [Kernel.map_comp, ← Kernel.comp_map, Kernel.comap_apply, Kernel.comp_apply',
    Kernel.comp_apply', Kernel.map_apply, Kernel.comap_apply, Kernel.map_apply,
  ]
  · simp
  all_goals try fun_prop
  all_goals measurability

end

end ProbabilityTheory.Kernel
