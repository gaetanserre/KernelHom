/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import LeanStoch.Mathlib.LIntegral
import LeanStoch.MonoidalComp.Quiver

open CategoryTheory MonoidalCategory MeasureTheory ProbabilityTheory MeasurableEquiv

class MeasurableCoherence (X Y : Type*) [MeasurableSpace X] [MeasurableSpace Y] where
  miso : X ≃ᵐ Y

namespace MeasurableCoherence

universe w x y

variable {X : Type x} {Y : Type y} [MeasurableSpace X] [MeasurableSpace Y]
  [mXY : MeasurableCoherence X Y]

instance : MeasurableCoherence X X where
  miso := MeasurableEquiv.refl X

noncomputable
def monoidalCoherence {X' Y' : Type w} [MeasurableSpace X'] [MeasurableSpace Y']
    (ex : X' ≃ᵐ X) (ey : Y' ≃ᵐ Y) : MonoidalCoherence (Stoch.of X') (Stoch.of Y') where
  iso := by
    let e := ex.trans <| mXY.miso.trans ey.symm
    refine ⟨⟨Kernel.id.map e, by kernel_sfinite⟩,
      ⟨Kernel.id.map e.symm, by kernel_sfinite⟩, ?_, ?_⟩
    all_goals kernel_cat
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

variable {W' : Type max w x y z} {X' : Type max w x y z} {Y' : Type max w x y z}
  {Z' : Type max w x y z} [MeasurableSpace W'] [MeasurableSpace X'] [MeasurableSpace Y']
  [MeasurableSpace Z'] (ew : W' ≃ᵐ W) (ex : X' ≃ᵐ X) (ey : Y' ≃ᵐ Y) (ez : Z' ≃ᵐ Z)

noncomputable
def monoComp' : Kernel W Z :=
  have := monoidalCoherence ex ey
  fromQuiver (ex := ew) (ey := ez) <| quiver (ex := ew) (ey := ex) κ ⊗≫
    quiver (ex := ey) (ey := ez) η

instance monoComp'_sfinite : IsSFiniteKernel (monoComp' κ η ew ex ey ez ) := by
  simp only [monoComp']
  infer_instance

/-- The kernelized version of the monoidal composition of kernels using
the `Stoch` monoidal category. -/
noncomputable
def monoComp : Kernel W Z :=
  monoComp' κ η (ulift.{_, max w x y z}) (ulift.{_, max w x y z})
    (ulift.{_, max w x y z}) (ulift.{_, max w x y z})

@[inherit_doc Kernel.monoComp]
scoped[ProbabilityTheory] infixr:80 " ⊗≫ₖ " => Kernel.monoComp

instance monoComp_sfinite : IsSFiniteKernel (κ ⊗≫ₖ η) := by
  simp only [monoComp]
  infer_instance

variable {W'' : Type max v w x y z} {X'' : Type max v w x y z} {Y'' : Type max v w x y z}
  {Z'' : Type max v w x y z} [MeasurableSpace W''] [MeasurableSpace X''] [MeasurableSpace Y'']
  [MeasurableSpace Z''] (ew' : W'' ≃ᵐ W) (ex' : X'' ≃ᵐ X) (ey' : Y'' ≃ᵐ Y) (ez' : Z'' ≃ᵐ Z)

lemma quiver_monoComp : @monoidalComp _ _ _ _ _ _ (monoidalCoherence ex' ey')
    (quiver (ex := ew') (ey := ex') κ) (quiver (ex := ey') (ey := ez') η)
    = quiver (ex := ew') (ey := ez') (monoComp κ η):= by
  simp only [monoComp, monoComp', fromQuiver, quiver, monoidalComp]
  kernel_cat
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
        · refine (Kernel.measurable_coe _ ?_).comp ?_
          · measurability
          · fun_prop
        · fun_prop
        · refine (Kernel.measurable_coe _ hs).comp ?_
          fun_prop
        · fun_prop
      · refine (Kernel.measurable_coe _ ?_).comp ?_
        · measurability
        · fun_prop
      · refine (Kernel.measurable_coe _ hs).comp ?_
        fun_prop
    all_goals try fun_prop
  all_goals try fun_prop
  all_goals try measurability

end ProbabilityTheory.Kernel
