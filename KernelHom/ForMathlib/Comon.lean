/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.CategoryTheory.Monoidal.Comon_

/-!
# Counit laws followed by a morphism

This file provides the counit laws of a comonoid object followed by a morphism, stated with tensor
products of morphisms. They are used by `kernel_disch`.

## Main declarations

* `ComonObj.comul_tensorHom_counit_comp`: `Δ ≫ (f ⊗ₘ (ε ≫ g)) = f ≫ ρ⁻¹ ≫ (𝟙 ⊗ₘ g)`.
* `ComonObj.comul_counit_comp_tensorHom`: `Δ ≫ ((ε ≫ g) ⊗ₘ f) = f ≫ λ⁻¹ ≫ (g ⊗ₘ 𝟙)`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace CategoryTheory.ComonObj

variable {C : Type*} [Category C] [MonoidalCategory C] {M Z Z' : C} [ComonObj M]

@[reassoc]
lemma comul_tensorHom_counit_comp (f : M ⟶ Z) (g : 𝟙_ C ⟶ Z') :
    Δ[M] ≫ (f ⊗ₘ (ε[M] ≫ g)) = f ≫ (ρ_ Z).inv ≫ (𝟙 Z ⊗ₘ g) := by
  rw [← comul_counit_hom_assoc, tensorHom_comp_tensorHom, Category.comp_id]

@[reassoc]
lemma comul_counit_comp_tensorHom (f : M ⟶ Z) (g : 𝟙_ C ⟶ Z') :
    Δ[M] ≫ ((ε[M] ≫ g) ⊗ₘ f) = f ≫ (λ_ Z).inv ≫ (g ⊗ₘ 𝟙 Z) := by
  rw [← counit_comul_hom_assoc, tensorHom_comp_tensorHom, Category.comp_id]

end CategoryTheory.ComonObj
