/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
import KernelHom.Tactic.Reassoc

/-!
-/

open ProbabilityTheory CategoryTheory

section

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (κ η : Kernel X Y) (h : κ = η)

include h in
@[reassoc]
lemma test : κ = η := h

#check test_assoc


example (h : κ = η) : κ = η := by
  test_handler h
  exact h

end

section

variable {C : Type*} [Category C] {X Y : C} (f g : X ⟶ Y) (h : f = g)

include h in
@[reassoc]
lemma test2 : f = g := h

#check test2_assoc

end
