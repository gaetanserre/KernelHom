/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Mathlib.CategoryTheory.MarkovCategory.Basic
import Mathlib.MeasureTheory.Category.MeasCat

open CategoryTheory

open scoped MonoidalCategory ComonObj

-- If true, fails to prove automatically some fields of `MonoidalCategory MeasCat`.
-- set_option mathlib.tactic.category.grind true

instance : MonoidalCategory MeasCat where
  tensorObj X Y := MeasCat.of (X × Y)
  whiskerLeft X Y₁ Y₂ f := ⟨Prod.map id f, measurable_id.prodMap f.2⟩
  whiskerRight f Y := ⟨Prod.map f id, f.2.prodMap measurable_id⟩
  tensorUnit := MeasCat.of Unit
  associator X Y Z :=
    ⟨⟨fun x ↦ (x.1.1, x.1.2, x.2), by fun_prop⟩,
      ⟨fun x ↦ ((x.1, x.2.1), x.2.2), by fun_prop⟩, rfl, rfl⟩
  leftUnitor X :=
    ⟨⟨Prod.snd, measurable_snd⟩, ⟨fun x ↦ ((), x), measurable_prodMk_left⟩, rfl, rfl⟩
  rightUnitor X :=
    ⟨⟨Prod.fst, measurable_fst⟩, ⟨fun x ↦ (x, ()), measurable_prodMk_right⟩, rfl, rfl⟩

-- Structure de comonoïde pour chaque objet : copy (diagonale) et discard (fonction constante)
instance (X : MeasCat) : ComonObj X where
  counit := ⟨fun _ ↦ (), measurable_const⟩
  comul := ⟨fun x ↦ (x, x), by fun_prop⟩


-- Le tressage : échange des composantes d'un produit
instance : BraidedCategory MeasCat where
  braiding X Y :=
    ⟨⟨fun (x, y) ↦ (y, x), by fun_prop⟩, ⟨fun (y, x) ↦ (x, y), by fun_prop⟩, rfl, rfl⟩

-- Le tressage est symétrique (swap ∘ swap = id)
instance : SymmetricCategory MeasCat where
  symmetry _ _ := rfl

-- Le comonoïde est commutatif (copy puis swap = copy)
instance (X : MeasCat) : IsCommComonObj X where
  comul_comm := rfl

instance : MarkovCategory MeasCat where
  discard_natural f := rfl
