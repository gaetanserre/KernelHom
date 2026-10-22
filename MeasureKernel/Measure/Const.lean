/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Measures as kernels

This file defines the transformation between measures and kernels from `Unit`, through the
constant kernel `Kernel.const Unit μ`.

## Main declarations

* `Kernel.const_congr`: two measures are equal if and only if their constant kernels are equal.
* `Kernel.id_prod_comp_const`: the composition-product `μ ⊗ₘ κ` as a composition of kernels.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.Kernel

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma const_congr (μ ν : Measure X) : μ = ν ↔ const Unit μ = const Unit ν :=
  ⟨fun h ↦ by rw [h], fun h ↦ by simpa using congrArg (fun κ ↦ κ ()) h⟩

/-- The equivalence between an equality of measures and the equality of their translations `κ` and
`η`, given by `const_congr`. -/
lemma const_congr_of_eq {μ ν : Measure X} {κ η : Kernel Unit X} (hκ : κ = const Unit μ)
    (hη : η = const Unit ν) :
    (μ = ν) = (κ = η) := by
  rw [hκ, hη, const_congr μ ν]

/-- The composition-product of a measure and a kernel, as a composition of kernels from `Unit`. -/
lemma id_prod_comp_const (μ : Measure X) [SFinite μ] (κ : Kernel X Y) [IsSFiniteKernel κ] :
    (Kernel.id ×ₖ κ) ∘ₖ const Unit μ = const Unit (μ ⊗ₘ κ) := by
  rw [comp_const, Measure.compProd_eq_comp_prod]

/-! ### Translation lemmas with hypotheses

The translation lemmas, with the translations of the subterms given as hypotheses. They are used by
the `measure_kernel` and `kernel_measure` tactics, so that each step of the translation is a single
application of these lemmas. -/

/-- The translation `κ ∘ₖ K` of `κ ∘ₘ μ`, from the translation `K` of `μ` (see `comp_const`). -/
lemma comp_const_of_eq {μ : Measure X} {K : Kernel Unit X} (κ : Kernel X Y)
    (hK : K = const Unit μ) :
    κ ∘ₖ K = const Unit (κ ∘ₘ μ) := by
  rw [hK, comp_const]

/-- The translation `(Kernel.id ×ₖ κ) ∘ₖ K` of `μ ⊗ₘ κ`, from the translation `K` of `μ` (see
`id_prod_comp_const`). -/
lemma id_prod_comp_const_of_eq {μ : Measure X} [SFinite μ] {K : Kernel Unit X} (κ : Kernel X Y)
    [IsSFiniteKernel κ] (hK : K = const Unit μ) :
    (Kernel.id ×ₖ κ) ∘ₖ K = const Unit (μ ⊗ₘ κ) := by
  rw [hK, id_prod_comp_const]

/-- The translation `K ×ₖ L` of `μ.prod ν`, from the translations `K` of `μ` and `L` of `ν` (see
`prod_const`). -/
lemma prod_const_of_eq {μ : Measure X} [SFinite μ] {ν : Measure Y} [SFinite ν] {K : Kernel Unit X}
    {L : Kernel Unit Y} (hK : K = const Unit μ) (hL : L = const Unit ν) :
    K ×ₖ L = const Unit (μ.prod ν) := by
  rw [hK, hL, prod_const]

end ProbabilityTheory.Kernel
