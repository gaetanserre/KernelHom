import Mathlib

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
  Hom X Y := Kernel X Y
  id X := Kernel.id
  comp κ₁ κ₂ := κ₂ ∘ₖ κ₁
  assoc κ₁ κ₂ κ₃ := by simp [Kernel.comp_assoc]

instance : MonoidalCategory MeasCatKer where
  tensorObj X Y := MeasCatKer.of (X × Y)
  whiskerLeft X Y₁ Y₂ κ := Kernel.id ∥ₖ κ
  whiskerRight κ Y := κ ∥ₖ Kernel.id
  tensorUnit := MeasCatKer.of Unit
  associator X Y Z := by
    have hf₁ : Measurable (fun (x : (X × Y) × Z) ↦ (x.1.1, x.1.2, x.2)) := by fun_prop
    have hf₂ : Measurable (fun (x : X × Y × Z) ↦ ((x.1, x.2.1), x.2.2)) := by fun_prop
    refine ⟨Kernel.id.map (fun x ↦ (x.1.1, x.1.2, x.2)),
      Kernel.id.map (fun x ↦ ((x.1, x.2.1), x.2.2)), ?_, ?_⟩
    · change (Kernel.id.map (fun x ↦ ((x.1, x.2.1), x.2.2)))
        ∘ₖ (Kernel.id.map (fun x ↦ (x.1.1, x.1.2, x.2))) = Kernel.id
      rw [Kernel.id_map hf₁, Kernel.id_map hf₂, Kernel.deterministic_comp_eq_map hf₂,
        Kernel.deterministic_map hf₁ hf₂]
      ext x s hs
      simp [Kernel.deterministic_apply, Kernel.id_apply]
    · change (Kernel.id.map (fun x ↦ (x.1.1, x.1.2, x.2)))
        ∘ₖ (Kernel.id.map (fun x ↦ ((x.1, x.2.1), x.2.2))) = Kernel.id
      rw [Kernel.id_map hf₂, Kernel.id_map hf₁, Kernel.deterministic_comp_eq_map hf₁,
        Kernel.deterministic_map hf₂ hf₁]
      ext x s hs
      simp [Kernel.deterministic_apply, Kernel.id_apply]
  leftUnitor X := by
    have hf₁ : Measurable (fun (x : X) ↦ ((), x)) := by fun_prop
    have hf₂ : Measurable (Prod.snd : Unit × X → X) := by fun_prop
    refine ⟨Kernel.id.map Prod.snd, Kernel.id.map (fun x ↦ ((), x)), ?_, ?_⟩
    · change (Kernel.id.map (fun x ↦ ((), x))) ∘ₖ (Kernel.id.map Prod.snd) = Kernel.id
      rw [Kernel.id_map hf₁, Kernel.deterministic_comp_eq_map hf₁, Kernel.id_map hf₂,
        Kernel.deterministic_map hf₂ hf₁]
      ext x s hs
      simp [Kernel.deterministic_apply, Kernel.id_apply]
    · change (Kernel.id.map Prod.snd) ∘ₖ (Kernel.id.map (fun x ↦ ((), x))) = Kernel.id
      rw [Kernel.id_map hf₂, Kernel.deterministic_comp_eq_map hf₂, Kernel.id_map hf₁,
        Kernel.deterministic_map hf₁ hf₂]
      ext x s hs
      simp [Kernel.deterministic_apply, Kernel.id_apply]
  rightUnitor X := by
    have hf₁ : Measurable (fun (x : X) ↦ (x, ())) := by fun_prop
    have hf₂ : Measurable (Prod.fst : X × Unit → X) := by fun_prop
    refine ⟨Kernel.id.map Prod.fst, Kernel.id.map (fun x ↦ (x, ())), ?_, ?_⟩
    · change (Kernel.id.map (fun x ↦ (x, ())) ∘ₖ (Kernel.id.map Prod.fst)) = Kernel.id
      rw [Kernel.id_map hf₁, Kernel.deterministic_comp_eq_map hf₁, Kernel.id_map hf₂,
        Kernel.deterministic_map hf₂ hf₁]
      ext x s hs
      simp [Kernel.deterministic_apply, Kernel.id_apply]
    · change (Kernel.id.map Prod.fst) ∘ₖ (Kernel.id.map (fun x ↦ (x, ()))) = Kernel.id
      rw [Kernel.id_map hf₂, Kernel.deterministic_comp_eq_map hf₂, Kernel.id_map hf₁,
        Kernel.deterministic_map hf₁ hf₂]
      ext x s hs
      simp [Kernel.deterministic_apply, Kernel.id_apply]

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
