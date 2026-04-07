/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import KernelHom.Mathlib.LIntegral
import KernelHom.Kernel.Hom

open CategoryTheory MeasureTheory ProbabilityTheory MeasurableEquiv

open scoped MonoidalCategory SFinKer

/-!
# Measurable coherence

This file introduces the monoidal composition for s-finite kernels (noted `⊗≫ₖ`).
## Main declarations

- `MeasurableCoherence`: class witnessing measurable equivalences between types.
- `monoComp`: monoidal composition of kernels using measurable equivalences to transport to
`SFinKer`.
- `hom_monoComp`: the `SFinKer` morphism of the kernelized monoidal composition is the monoidal
composition of the morphisms in `SFinKer`.
-/

/-- A class witnessing the existence of a measurable equivalence between two measurable spaces. -/
-- ANCHOR: MeasurableCoherence
class MeasurableCoherence (X Y : Type*) [MeasurableSpace X] [MeasurableSpace Y] where
  /-- A measurable equivalence between `X` and `Y`. -/
  miso : X ≃ᵐ Y
-- ANCHOR_END: MeasurableCoherence

namespace MeasurableCoherence

universe w x y

variable {X : Type x} {Y : Type y} [MeasurableSpace X] [MeasurableSpace Y]
  [mXY : MeasurableCoherence X Y]

instance : MeasurableCoherence X X where
  miso := MeasurableEquiv.refl X

/-- `MeasurableCoherence` gives an instance of `MonoidalCoherence` in the `SFinKer` category. -/
-- ANCHOR: monoidalCoherence
@[reducible]
noncomputable def monoidalCoherence {X' Y' : Type w} [MeasurableSpace X'] [MeasurableSpace Y']
    (ex : X' ≃ᵐ X) (ey : Y' ≃ᵐ Y) : MonoidalCoherence (SFinKer.of X') (SFinKer.of Y') where
  iso := by
    let e := ex.trans <| mXY.miso.trans ey.symm
    refine ⟨⟨Kernel.id.map e, inferInstance⟩,
      ⟨Kernel.id.map e.symm, inferInstance⟩, ?_, ?_⟩
    all_goals ext; dsimp
    · rw [Kernel.id_map (by fun_prop), Kernel.id_map (by fun_prop),
        Kernel.deterministic_comp_deterministic, Kernel.id]
      congr
      simp [e]
    · rw [Kernel.id_map (by fun_prop), Kernel.id_map (by fun_prop),
        Kernel.deterministic_comp_deterministic, Kernel.id]
      congr
      simp [e]
-- ANCHOR_END: monoidalCoherence

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

/-- The kernelized version of the monoidal composition of kernels using the `SFinKer` category.
It uses arbitrary measurable equivalences to transport the kernels to the `SFinKer` category. -/
noncomputable def monoComp₀ : Kernel W Z :=
  have := monoidalCoherence ex ey
  fromHom (ex := ew) (ey := ez) <| hom (ex := ew) (ey := ex) κ ⊗≫
    hom (ex := ey) (ey := ez) η

instance monoComp'_sfinite : IsSFiniteKernel (monoComp₀ κ η ew ex ey ez ) := by
  simp only [monoComp₀]
  infer_instance

/-- The kernelized version of the monoidal composition of kernels using the `SFinKer` category. -/
-- ANCHOR: monoComp
noncomputable abbrev monoComp : Kernel W Z :=
  monoComp₀ κ η (ulift.{_, max w x y z}) (ulift.{_, max w x y z})
    (ulift.{_, max w x y z}) (ulift.{_, max w x y z})
-- ANCHOR_END: monoComp

-- ANCHOR: monoComp_infix
@[inherit_doc Kernel.monoComp]
scoped[ProbabilityTheory] infixr:80 " ⊗≫ₖ " => Kernel.monoComp
-- ANCHOR_END: monoComp_infix

instance monoComp_sfinite : IsSFiniteKernel (κ ⊗≫ₖ η) := by
  infer_instance

variable {W'' : Type max v w x y z} {X'' : Type max v w x y z} {Y'' : Type max v w x y z}
  {Z'' : Type max v w x y z} [MeasurableSpace W''] [MeasurableSpace X''] [MeasurableSpace Y'']
  [MeasurableSpace Z''] (ew' : W'' ≃ᵐ W) (ex' : X'' ≃ᵐ X) (ey' : Y'' ≃ᵐ Y) (ez' : Z'' ≃ᵐ Z)

lemma hom_monoComp : @monoidalComp _ _ _ _ _ _ (monoidalCoherence ex' ey')
    (hom (ex := ew') (ey := ex') κ) (hom (ex := ey') (ey := ez') η)
    = hom (ex := ew') (ey := ez') (monoComp κ η):= by
  simp only [monoComp₀, fromHom, hom, monoidalComp]
  ext _ s hs; dsimp
  unfold monoidalCoherence
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
