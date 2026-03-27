/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Mathlib.MeasureTheory.MeasurableSpace.Embedding

namespace MeasurableEquiv

universe w x y

variable {X : Type x} {Y : Type y} [MeasurableSpace X] [MeasurableSpace Y]
  {X' Y' : Type w} [MeasurableSpace X'] [MeasurableSpace Y'] (ex : X' ≃ᵐ X) (ey : Y' ≃ᵐ Y)

def prod : X' × Y' ≃ᵐ X × Y where
  toFun := fun (x', y') ↦ (ex x', ey y')
  invFun := fun (x, y) ↦ (ex.symm x, ey.symm y)
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]
  measurable_toFun := by fun_prop
  measurable_invFun := by fun_prop

def punit : PUnit.{w + 1} ≃ᵐ PUnit.{x + 1} where
  toFun := fun _ ↦ PUnit.unit
  invFun := fun _ ↦ PUnit.unit
  left_inv := by grind
  right_inv := by grind
  measurable_toFun := measurable_id
  measurable_invFun := measurable_id

end MeasurableEquiv
