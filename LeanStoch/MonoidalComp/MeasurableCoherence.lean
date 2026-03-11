/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Mathlib
import LeanStoch.MonoidalComp.Kernel
import LeanStoch.Tactics.Tactics

open CategoryTheory MonoidalCategory MeasureTheory ProbabilityTheory

class MeasurableCoherence (X Y : Type*) [MeasurableSpace X] [MeasurableSpace Y] where
  miso : X ≃ᵐ Y

namespace MeasurableCoherence

universe w x y

variable {X : Type x} {Y : Type y} [MeasurableSpace X] [MeasurableSpace Y]
  [mXY : MeasurableCoherence X Y]

noncomputable
instance monoidalCoherence : MonoidalCoherence (Stoch.of (ULift.{max w y} X))
    (Stoch.of (ULift.{max w x} Y)) where
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

universe w x y z

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

end ProbabilityTheory.Kernel

variable {W X Y Z : Type*}
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace W]
  [MeasurableCoherence X Y] (κ : Kernel W X) [IsSFiniteKernel κ] (η : Kernel Y Z)
  [IsSFiniteKernel η]

#check κ ⊗≫ₖ η
