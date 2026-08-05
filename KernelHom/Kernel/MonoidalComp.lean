/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import KernelHom.ForMathlib.LIntegral
public import KernelHom.Kernel.Hom

/-!
# Measurable coherence

This file introduces the monoidal composition for s-finite kernels (noted `⊗≫ₖ`).
## Main declarations

* `MeasurableCoherence`: class witnessing measurable equivalences between types.
* `monoComp`: monoidal composition of kernels using measurable equivalences to transport to
  `SFinKer`.
* `hom_monoComp`: the `SFinKer` morphism of the kernelized monoidal composition is the monoidal
  composition of the morphisms in `SFinKer`.
-/

@[expose] public section

open CategoryTheory MeasureTheory ProbabilityTheory MeasurableEquiv

open scoped MonoidalCategory SFinKer

/-- A class witnessing the existence of a measurable equivalence between two measurable spaces. -/
class MeasurableCoherence (X Y : Type*) [MeasurableSpace X] [MeasurableSpace Y] where
  /-- A measurable equivalence between `X` and `Y`. -/
  miso : X ≃ᵐ Y

namespace MeasurableCoherence

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] [mXY : MeasurableCoherence X Y]

instance : MeasurableCoherence X X where
  miso := MeasurableEquiv.refl X

@[reducible]
def equiv_trans {X' Y' : Type*} [MeasurableSpace X'] [MeasurableSpace Y']
    (ex : X' ≃ᵐ X) (ey : Y' ≃ᵐ Y) : MeasurableCoherence X' Y' where
  miso := ex.trans <| mXY.miso.trans ey.symm

/-- `MeasurableCoherence` gives an instance of `MonoidalCoherence` in the `SFinKer` category. -/
@[reducible]
noncomputable def monoidalCoherence {SX SY : SFinKer} (ex : SX.carrier ≃ᵐ X)
    (ey : SY.carrier ≃ᵐ Y) : MonoidalCoherence SX SY where
  iso := by
    let e := ex.trans <| mXY.miso.trans ey.symm
    refine ⟨⟨Kernel.id.map e, inferInstance⟩,
      ⟨Kernel.id.map e.symm, inferInstance⟩, ?_, ?_⟩
    all_goals ext; dsimp
    · rw [Kernel.id_map (by fun_prop), Kernel.id_map (by fun_prop),
        Kernel.deterministic_comp_deterministic, Kernel.id]
      congr
      simp
    · rw [Kernel.id_map (by fun_prop), Kernel.id_map (by fun_prop),
        Kernel.deterministic_comp_deterministic, Kernel.id]
      congr
      simp

end MeasurableCoherence

namespace ProbabilityTheory.Kernel

open MeasurableCoherence

variable {W X Y Z : Type*} [MeasurableSpace W] [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace Z] {SW SX SY SZ : SFinKer} (ew : SW ≃ᵐ W) (ex : SX ≃ᵐ X)
  (ey : SY ≃ᵐ Y) (ez : SZ ≃ᵐ Z) [MeasurableCoherence X Y] (κ : Kernel W X) [IsSFiniteKernel κ]
  (η : Kernel Y Z) [IsSFiniteKernel η]

/-- The kernelized version of the monoidal composition of kernels using the `SFinKer` category.
It uses arbitrary measurable equivalences to transport the kernels to the `SFinKer` category. -/
noncomputable def monoComp₀ : Kernel W Z :=
  have := monoidalCoherence ex ey
  fromHom (ex := ew) (ey := ez) <| hom (ex := ew) (ey := ex) κ ⊗≫
    hom (ex := ey) (ey := ez) η

instance monoComp'_sfinite : IsSFiniteKernel (monoComp₀ ew ex ey ez κ η) := by
  simp only [monoComp₀]
  infer_instance

/-- The kernelized version of the monoidal composition of kernels using the `SFinKer` category. -/
noncomputable abbrev monoComp : Kernel W Z :=
  monoComp₀
    (SW := SFinKer.of <| ULift W)
    (SX := SFinKer.of <| ULift X)
    (SY := SFinKer.of <| ULift Y)
    (SZ := SFinKer.of <| ULift Z)
    ulift.{_, max u_1 u_2 u_3 u_4}
    ulift.{_, max u_1 u_2 u_3 u_4}
    ulift.{_, max u_1 u_2 u_3 u_4}
    ulift.{_, max u_1 u_2 u_3 u_4}
    κ η

@[inherit_doc Kernel.monoComp]
scoped[ProbabilityTheory] infixr:80 " ⊗≫ₖ " => Kernel.monoComp

variable {W X Y Z : Type u} [MeasurableSpace W] [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace Z] {SW SX SY SZ : SFinKer} (ew : SW ≃ᵐ W) (ex : SX ≃ᵐ X)
  (ey : SY ≃ᵐ Y) (ez : SZ ≃ᵐ Z) [mXY : MeasurableCoherence X Y]

variable {W₀ X₀ Y₀ Z₀ : Type*} [MeasurableSpace W₀] [MeasurableSpace X₀] [MeasurableSpace Y₀]
  [MeasurableSpace Z₀] {ew₀ : W ≃ᵐ W₀} {ex₀ : X ≃ᵐ X₀} {ey₀ : Y ≃ᵐ Y₀}
  {ez₀ : Z ≃ᵐ Z₀} {κ : Kernel W₀ X₀} [IsSFiniteKernel κ] {η : Kernel Y₀ Z₀} [IsSFiniteKernel η]
  [MeasurableCoherence X₀ Y₀]

lemma hom_monoComp' : @monoidalComp _ _ _ _ _ _ (monoidalCoherence ex ey)
    (hom (ex := ew) (ey := ex) (lift κ (ex := ew₀) (ey := ex₀)))
    (hom (ex := ey) (ey := ez) (lift η (ex := ey₀) (ey := ez₀)))
    = hom (ex := ew) (ey := ez) (lift (monoComp κ η) (ex := ew₀) (ey := ez₀)) := by
  sorry

end ProbabilityTheory.Kernel
