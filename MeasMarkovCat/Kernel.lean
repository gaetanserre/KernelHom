import Mathlib
import MeasMarkovCat.Tactics

open CategoryTheory ProbabilityTheory

universe u

structure MeasCatKer : Type (u + 1) where
  of ::
  carrier : Type u
  [str : MeasurableSpace carrier]

attribute [instance] MeasCatKer.str

instance : CoeSort MeasCatKer Type* :=
  ⟨MeasCatKer.carrier⟩

noncomputable section

instance : LargeCategory MeasCatKer where
  Hom X Y := { k : Kernel X Y // IsSFiniteKernel k }
  id X := ⟨Kernel.id, by kernel_sfiniteness⟩
  comp κ₁ κ₂ := ⟨κ₂.1 ∘ₖ κ₁.1, by kernel_sfiniteness⟩
  assoc κ₁ κ₂ κ₃ := by simp [Kernel.comp_assoc]

instance : MonoidalCategory MeasCatKer where
  tensorObj X Y := MeasCatKer.of (X × Y)
  whiskerLeft X Y₁ Y₂ κ := ⟨Kernel.id ∥ₖ κ.1, by kernel_sfiniteness⟩
  whiskerRight κ Y := ⟨κ.1 ∥ₖ Kernel.id, by kernel_sfiniteness⟩
  tensorUnit := MeasCatKer.of Unit
  associator X Y Z := by
    let f₁ := fun (x : (X × Y) × Z) ↦ (x.1.1, x.1.2, x.2)
    let f₂ := fun (x : X × Y × Z) ↦ ((x.1, x.2.1), x.2.2)
    have hf₁ : Measurable f₁ := by fun_prop
    have hf₂ : Measurable f₂ := by fun_prop
    refine ⟨⟨Kernel.id.map f₁, by kernel_sfiniteness⟩,
      ⟨Kernel.id.map f₂, by kernel_sfiniteness⟩, ?_, ?_⟩
    · refine Subtype.ext ?_
      change Kernel.id.map f₂ ∘ₖ Kernel.id.map f₁ = Kernel.id
      rw [Kernel.id_map hf₁, Kernel.id_map hf₂, Kernel.deterministic_comp_eq_map hf₂,
        Kernel.deterministic_map hf₁ hf₂]
      ext x s hs
      simp [Kernel.deterministic_apply, Kernel.id_apply, f₁, f₂]
    · refine Subtype.ext ?_
      change Kernel.id.map f₁ ∘ₖ Kernel.id.map f₂ = Kernel.id
      rw [Kernel.id_map hf₂, Kernel.id_map hf₁, Kernel.deterministic_comp_eq_map hf₁,
        Kernel.deterministic_map hf₂ hf₁]
      ext x s hs
      simp [Kernel.deterministic_apply, Kernel.id_apply, f₁, f₂]
  leftUnitor X := by
    let f₁ := fun (x : X) ↦ ((), x)
    have hf₁ : Measurable f₁ := by fun_prop
    have hf₂ : Measurable (Prod.snd : Unit × X → X) := by fun_prop
    refine ⟨⟨Kernel.id.map Prod.snd, by kernel_sfiniteness⟩,
      ⟨Kernel.id.map f₁, by kernel_sfiniteness⟩, ?_, ?_⟩
    · refine Subtype.ext ?_
      change Kernel.id.map f₁ ∘ₖ Kernel.id.map Prod.snd = Kernel.id
      rw [Kernel.id_map hf₁, Kernel.deterministic_comp_eq_map hf₁, Kernel.id_map hf₂,
        Kernel.deterministic_map hf₂ hf₁]
      ext x s hs
      simp [Kernel.deterministic_apply, Kernel.id_apply, f₁]
    · refine Subtype.ext ?_
      change Kernel.id.map Prod.snd ∘ₖ Kernel.id.map f₁ = Kernel.id
      rw [Kernel.id_map hf₂, Kernel.deterministic_comp_eq_map hf₂, Kernel.id_map hf₁,
        Kernel.deterministic_map hf₁ hf₂]
      ext x s hs
      simp [Kernel.deterministic_apply, Kernel.id_apply, f₁]
  rightUnitor X := by
    let f₁ := fun (x : X) ↦ (x, ())
    have hf₁ : Measurable f₁ := by fun_prop
    have hf₂ : Measurable (Prod.fst : X × Unit → X) := by fun_prop
    refine ⟨⟨Kernel.id.map Prod.fst, by kernel_sfiniteness⟩,
      ⟨Kernel.id.map f₁, by kernel_sfiniteness⟩, ?_, ?_⟩
    · refine Subtype.ext ?_
      change (Kernel.id.map f₁ ∘ₖ Kernel.id.map Prod.fst) = Kernel.id
      rw [Kernel.id_map hf₁, Kernel.deterministic_comp_eq_map hf₁, Kernel.id_map hf₂,
        Kernel.deterministic_map hf₂ hf₁]
      ext x s hs
      simp [Kernel.deterministic_apply, Kernel.id_apply, f₁]
    · refine Subtype.ext ?_
      change Kernel.id.map Prod.fst ∘ₖ Kernel.id.map f₁ = Kernel.id
      rw [Kernel.id_map hf₂, Kernel.deterministic_comp_eq_map hf₂, Kernel.id_map hf₁,
        Kernel.deterministic_map hf₁ hf₂]
      ext x s hs
      simp [Kernel.deterministic_apply, Kernel.id_apply, f₁]

  -- Might need to change the type of morphisms to `SFiniteKernel`.
  whiskerLeft_id X Y := by sorry
  id_whiskerRight := by sorry
  id_tensorHom_id := by sorry
  tensorHom_comp_tensorHom := by sorry
  associator_naturality := by sorry
  pentagon := by sorry
  leftUnitor_naturality := by sorry
  rightUnitor_naturality := by sorry
  triangle := by sorry

-- Use `ProbabilityTheory.Kernel.copy` in the `ComonObj` instance.

end
