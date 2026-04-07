/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Measurable equivalences

This file extends the theory of measurable equivalences, providing utilities for
working with products and other structures.

## Main declarations

- `MeasurableEquiv.prod`: product of measurable equivalences.
- `MeasurableEquiv.punit`: measurable equivalence between `PUnit`s.
-/

namespace MeasurableEquiv

universe w x y

variable {X : Type x} {Y : Type y} [MeasurableSpace X] [MeasurableSpace Y]
  {X' Y' : Type w} [MeasurableSpace X'] [MeasurableSpace Y'] (ex : X' ≃ᵐ X) (ey : Y' ≃ᵐ Y)

/-- The product of two measurable equivalences is a measurable equivalence. -/
def prod : X' × Y' ≃ᵐ X × Y where
  toFun := fun (x', y') ↦ (ex x', ey y')
  invFun := fun (x, y) ↦ (ex.symm x, ey.symm y)
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]
  measurable_toFun := by simp only [Equiv.coe_fn_mk]; fun_prop
  measurable_invFun := by simp only [Equiv.coe_fn_symm_mk]; fun_prop

/-- The measurable equivalence between two `PUnit`s. -/
def punit : PUnit.{w + 1} ≃ᵐ PUnit.{x + 1} where
  toFun := fun _ ↦ PUnit.unit
  invFun := fun _ ↦ PUnit.unit
  left_inv := by grind
  right_inv := by grind
  measurable_toFun := measurable_id
  measurable_invFun := measurable_id

end MeasurableEquiv
