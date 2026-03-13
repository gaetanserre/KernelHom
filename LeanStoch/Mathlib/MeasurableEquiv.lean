/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Mathlib.MeasureTheory.MeasurableSpace.Embedding

namespace MeasurableEquiv

universe w x y

variable {X : Type x} {Y : Type y} [MeasurableSpace X] [MeasurableSpace Y]

def ulift_prod : ULift.{max w y} X × ULift.{max w x} Y ≃ᵐ X × Y where
  toFun := fun (⟨x⟩, ⟨y⟩) ↦ (x, y)
  invFun := fun (x, y) ↦ (ULift.up x, ULift.up y)
  left_inv := by rintro ⟨⟨x⟩, ⟨y⟩⟩; rfl
  right_inv := by rintro ⟨x, y⟩; rfl
  measurable_toFun := by
    have := measurable_down.{_, max w y} (α := X)
    have := measurable_down.{_, max w x} (α := Y)
    fun_prop
  measurable_invFun := by
    have := measurable_up.{_, max w y} (α := X)
    have := measurable_up.{_, max w x} (α := Y)
    fun_prop

end MeasurableEquiv
