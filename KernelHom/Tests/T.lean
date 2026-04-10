import Mathlib

open CategoryTheory Bicategory

abbrev adjointifyCounit_hom {B : Type u} [Bicategory B] {a b : B} {f : a ⟶ b}
  {g : b ⟶ a} (η : 𝟙 a ≅ f ≫ g) (e : g ≫ f ≅ 𝟙 b) : g ≫ f ⟶ 𝟙 b :=
    g ◁ ((ρ_ f).inv ≫ rightZigzag e.inv η.inv ≫ (λ_ f).hom) ≫ e.hom

theorem adjointifyCounit_left_triangle {B : Type u} [Bicategory B] {a b : B}
    {f : a ⟶ b} {g : b ⟶ a} (η : 𝟙 a ≅ f ≫ g) (e : g ≫ f ≅ 𝟙 b) :
    leftZigzag η.hom (adjointifyCounit_hom η e) = (λ_ f).hom ≫ (ρ_ f).inv := by
  with_panel_widgets [Mathlib.Tactic.Widget.StringDiagram]
  calc
    _ = 𝟙 (𝟙 a ≫ f) ⊗≫ (η.hom ▷ (f ≫ 𝟙 b) ≫ (f ≫ g) ◁ f ◁ e.inv) ⊗≫
          f ◁ g ◁ η.inv ▷ f ⊗≫ f ◁ e.hom := by
      bicategory
    _ = 𝟙 (𝟙 a ≫ f) ⊗≫ f ◁ e.inv ⊗≫
          (η.hom ▷ (f ≫ g) ≫ (f ≫ g) ◁ η.inv) ▷ f ⊗≫ f ◁ e.hom := by
      rw [← whisker_exchange η.hom (f ◁ e.inv)]
      bicategory
    _ = 𝟙 (𝟙 a ≫ f) ⊗≫ f ◁ e.inv ⊗≫ (η.inv ≫ η.hom) ▷ f ⊗≫ f ◁ e.hom := by
      rw [← whisker_exchange η.hom η.inv]
      bicategory
    _ = 𝟙 (𝟙 a ≫ f) ⊗≫ f ◁ (e.inv ≫ e.hom) := by
      rw [Iso.inv_hom_id]
      bicategory
    _ = _ := by
      rw [Iso.inv_hom_id]
      bicategory
