/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Mathlib
import LeanStoch.Stoch
import LeanStoch.Tactics

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.Kernel

universe w x y

variable {X : Type x} {Y : Type y} [MeasurableSpace X] [MeasurableSpace Y]


noncomputable
def fromQuiver (κ : Stoch.of (ULift.{max w y} X) ⟶ Stoch.of (ULift.{max w x} Y)) : Kernel X Y :=
  (κ.1.comap MeasurableEquiv.ulift.symm (by fun_prop)).map MeasurableEquiv.ulift

@[simp]
lemma fromQuiver_sfinite (κ : Stoch.of (ULift.{max w y} X) ⟶ Stoch.of (ULift.{max w x} Y)) :
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
  sorry

open CategoryTheory in
lemma toQuiver_comp.{v} {Z : Type w} [MeasurableSpace Z] {κ₁ : Kernel X Y} {κ₂ : Kernel Z X}
    [IsSFiniteKernel κ₁] [IsSFiniteKernel κ₂] :
    toQuiver.{max v w x y} (κ₁ ∘ₖ κ₂) = toQuiver.{max v w x y} κ₂ ≫ toQuiver.{max v w x y} κ₁ := by
  sorry


/- open CategoryTheory in
@[simp]
lemma toQuiver_comp_iff {Z : Type w} [MeasurableSpace Z] {κ₁ : Kernel X Y} {κ₂ : Kernel Z X}
    {κ₃ : Kernel Z Y} [IsSFiniteKernel κ₁] [IsSFiniteKernel κ₂] [IsSFiniteKernel κ₃] :
    κ₁ ∘ₖ κ₂ = κ₃ ↔ toQuiver.{max w x y} κ₂ ≫ κ₁.toQuiver = κ₃.toQuiver := by
  sorry -/

@[simp]
lemma toQuiver_eq_iff {κ₁ κ₂ : Kernel X Y} [IsSFiniteKernel κ₁] [IsSFiniteKernel κ₂] :
    κ₁.toQuiver = κ₂.toQuiver ↔ κ₁ = κ₂ := by
  sorry

end ProbabilityTheory.Kernel
