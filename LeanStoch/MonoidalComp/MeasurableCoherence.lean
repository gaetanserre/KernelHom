/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Mathlib
import LeanStoch.MonoidalComp.Kernel
import LeanStoch.Tactic.Tactic

open CategoryTheory MonoidalCategory MeasureTheory ProbabilityTheory

class MeasurableCoherence (X Y : Type*) [MeasurableSpace X] [MeasurableSpace Y] where
  miso : X ≃ᵐ Y

namespace MeasurableCoherence

universe w x y

variable {X : Type x} {Y : Type y} [MeasurableSpace X] [MeasurableSpace Y]
  [mXY : MeasurableCoherence X Y]

noncomputable
instance monoidalCoherence : MonoidalCoherence (Stoch.of (ULift.{max w y x} X))
    (Stoch.of (ULift.{max w x y} Y)) where
  iso := by
    -- ULift X ≃ᵐ X ≃ᵐ Y ≃ᵐ ULift Y
    let e : ULift X ≃ᵐ ULift Y :=
      MeasurableEquiv.ulift.trans <| mXY.miso.trans MeasurableEquiv.ulift.symm
    refine ⟨⟨Kernel.id.map e, by kernel_sfinite⟩,
      ⟨Kernel.id.map e.symm, by kernel_sfinite⟩, ?_, ?_⟩
    all_goals cat_kernel
    · rw [Kernel.id_map (by fun_prop), Kernel.id_map (by fun_prop),
        Kernel.deterministic_comp_deterministic, Kernel.id_eq_deterministic_id]
      congr
      simp [e]
    · rw [Kernel.id_map (by fun_prop), Kernel.id_map (by fun_prop),
        Kernel.deterministic_comp_deterministic, Kernel.id_eq_deterministic_id]
      congr
      simp [e]

end MeasurableCoherence

namespace ProbabilityTheory.Kernel

open MeasurableCoherence

universe v w x y z

variable {W : Type w} {X : Type x} {Y : Type y} {Z : Type z}
  [MeasurableSpace W] [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  [MeasurableCoherence X Y] (κ : Kernel W X) [IsSFiniteKernel κ] (η : Kernel Y Z)
  [IsSFiniteKernel η]

noncomputable
def monoComp : Kernel W Z := by
  have := monoidalCoherence.{max w x y z} (X := X) (Y := Y)
  exact fromQuiver.{max w x y z} <| toQuiver.{max w x y z} κ ⊗≫ toQuiver.{max w x y z} η

@[inherit_doc Kernel.monoComp]
scoped[ProbabilityTheory] infixr:80 " ⊗≫ₖ " =>
  Kernel.monoComp

instance monoComp_sfinite : IsSFiniteKernel (κ ⊗≫ₖ η) := by
  simp only [monoComp]
  infer_instance

/- lemma toQuiver_monoComp : toQuiver.{max v w x y z} (monoComp κ η) =
    @monoidalComp _ _ _ _ _ _ (monoidalCoherence.{max v w x y z} (X := X) (Y := Y))
    (toQuiver.{max v w x y z} κ) (toQuiver.{max v w x y z} η) := by
  sorry -/

end ProbabilityTheory.Kernel

variable {W X Y Z : Type*}
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace W]
  [MeasurableCoherence X Y] (κ : Kernel W X) [IsSFiniteKernel κ] (η : Kernel Y Z)
  [IsSFiniteKernel η]

#check κ ⊗≫ₖ η

example {X Y Z : Stoch} (f : 𝟙_ Stoch ⟶ X) (g : Y ⟶ Z) [MonoidalCoherence X Y] :
    (λ_ (𝟙_ Stoch)).hom ≫ f ⊗≫ g = (ρ_ (𝟙_ Stoch)).hom ≫ f ⊗≫ g := by
  coherence

def f.{u, v} {α : Type u} {β : Type v} (self : α × β) : α := Prod.fst self
def g.{u, v} {α : Type u} {β : Type v} (self : α × β) : β := Prod.snd self

example (κ : Kernel Unit X) [IsSFiniteKernel κ] (η : Kernel Y Z)
    [IsSFiniteKernel η] [MeasurableCoherence X Y] :
    κ ∘ₖ (Kernel.id.map f : Kernel (Unit × Unit) Unit) ⊗≫ₖ η = κ ∘ₖ (Kernel.id.map g) ⊗≫ₖ η := by
  kernel_coherence
