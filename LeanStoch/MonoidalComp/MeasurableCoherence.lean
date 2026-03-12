/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import LeanStoch.Mathlib.LIntegral
import LeanStoch.MonoidalComp.Kernel

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
    let e : ULift.{max w x y} X ≃ᵐ ULift.{max w x y} Y :=
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

/-- The kernelized version of the monoidal composition of kernels using
the `Stoch` monoidal category. -/
noncomputable
def monoComp : Kernel W Z :=
  have := monoidalCoherence.{max w x y z} (X := X) (Y := Y)
  fromQuiver.{max w x y z} <| toQuiver.{max w x y z} κ ⊗≫ toQuiver.{max w x y z} η

@[inherit_doc Kernel.monoComp]
scoped[ProbabilityTheory] infixr:80 " ⊗≫ₖ " => Kernel.monoComp

instance monoComp_sfinite : IsSFiniteKernel (κ ⊗≫ₖ η) := by
  simp only [monoComp]
  infer_instance

lemma toQuiver_monoComp : toQuiver.{max v w x y z} (monoComp κ η) =
    @monoidalComp _ _ _ _ _ _ (monoidalCoherence.{max v w x y z} (X := X) (Y := Y))
    (toQuiver.{max v w x y z} κ) (toQuiver.{max v w x y z} η) := by
  simp only [monoComp, fromQuiver, toQuiver, monoidalComp]
  cat_kernel
  dsimp [monoidalCoherence]
  ext _ s hs
  simp_all only [coe_comap, Function.comp_apply, comp_apply']
  rw [Kernel.map_apply', Kernel.map_apply']
  · simp_all only [coe_comap, Function.comp_apply, MeasurableEquiv.measurableSet_preimage,
    comp_apply', MeasurableEquiv.apply_symm_apply]
    rw [Kernel.map_apply, Kernel.map_apply, Kernel.id_map (by fun_prop),
      Kernel.id_map (by fun_prop)]
    · simp_rw [Kernel.deterministic_apply]
      rw [lintegral_lintegral_dirac, lintegral_lintegral_dirac]
      · rw [MeasureTheory.lintegral_map, MeasureTheory.lintegral_map]
        · simp_all only [MeasurableEquiv.trans_apply, MeasurableEquiv.apply_symm_apply]
          congr with _
          rw [Kernel.map_apply', Kernel.map_apply']
          · simp
          all_goals try fun_prop
          all_goals try measurability
        · refine ((η.map MeasurableEquiv.ulift.symm).measurable_coe hs).comp ?_
          fun_prop
        · fun_prop
        · refine ((η.map MeasurableEquiv.ulift.symm).measurable_coe ?_).comp ?_
          · measurability
          · fun_prop
        · fun_prop
      · refine ((η.map ⇑MeasurableEquiv.ulift.symm).measurable_coe hs).comp ?_
        fun_prop
      · refine ((η.map ⇑MeasurableEquiv.ulift.symm).measurable_coe ?_).comp ?_
        · measurability
        · fun_prop
    all_goals try fun_prop
  all_goals try fun_prop
  all_goals try measurability

end ProbabilityTheory.Kernel
