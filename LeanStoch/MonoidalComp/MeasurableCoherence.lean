/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Mathlib
import LeanStoch.Stoch
import LeanStoch.Tactics

open CategoryTheory MonoidalCategory MeasureTheory ProbabilityTheory

class MeasurableCoherence (X Y : Type*) [MeasurableSpace X] [MeasurableSpace Y] where
  miso : X ≃ᵐ Y

namespace MeasurableCoherence

universe x y

variable {X : Type x} {Y : Type y} [MeasurableSpace X] [MeasurableSpace Y]
  [mXY : MeasurableCoherence X Y]

noncomputable
instance : MonoidalCoherence (C := (Stoch : Type (max x y + 1)))
    (Stoch.of <| ULift X) (Stoch.of <| ULift Y) where
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
  [MeasurableCoherence X Y]
  (κ : Kernel W X) [IsSFiniteKernel κ] (η : Kernel Y Z) [IsSFiniteKernel η]

noncomputable
def monoComp : Kernel W Z := by
  let SUW := Stoch.of (ULift.{max w x y z} W)
  let SUX := Stoch.of (ULift.{max w x y z} X)
  let SUY := Stoch.of (ULift.{max w x y z} Y)
  let SUZ := Stoch.of (ULift.{max w x y z} Z)
  let κ' : SUW ⟶ SUX := by
    refine ⟨(κ.comap MeasurableEquiv.ulift (by fun_prop)).map MeasurableEquiv.ulift.symm, ?_⟩
    kernel_sfinite
  let η' : SUY ⟶ SUZ := by
    refine ⟨(η.comap MeasurableEquiv.ulift (by fun_prop)).map MeasurableEquiv.ulift.symm, ?_⟩
    kernel_sfinite
  have : MonoidalCoherence SUX SUY := by sorry
  let test := κ' ⊗≫ η'
  let t : Kernel W SUZ := test.1.comap MeasurableEquiv.ulift.symm (by fun_prop)
  exact t.map MeasurableEquiv.ulift


end ProbabilityTheory.Kernel

universe u v

variable {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableCoherence X Y]

noncomputable
example : MonoidalCoherence (C := (Stoch : Type (max u v + 1)))
    (Stoch.of <| ULift X) (Stoch.of <| ULift Y) := inferInstance

variable {W X Y Z : Stoch} [MonoidalCoherence X Y] (κ : W ⟶ X) (η : Y ⟶ Z)

#check κ ⊗≫ η
