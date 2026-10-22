/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import KernelHom
public import Mathlib.Probability.Kernel.Posterior
public import Mathlib.Probability.Kernel.Invariance

/-!
# Reversibility of data augmentation

This file formalizes Lemma 2.3.5 of [R. Douc, E. Moulines, P. Priouret and P. Soulier, *Markov
Chains*, Springer, 2018]. A data augmentation algorithm writes a distribution `π` on `X` as the
marginal of a distribution on `X × Y` with two disintegrations,
`π(dx) R(x, dy) = π'(dy) S(y, dx)`, where `R : Kernel X Y` and `S : Kernel Y X`. The algorithm
draws `y` from `R(x)`, then `x` from `S(y)`, so that the sequence of the `x` is a Markov chain with
kernel `RS`, written `S ∘ₖ R` in Mathlib. The lemma states that `π` is reversible with respect to
this kernel.

The proof of the book computes `(π ⊗ RS)(A × B) = ∫ S(y, A) S(y, B) dπ'(y)`, which is symmetric in
`A` and `B`. The proof below follows the same steps on the measures seen as kernels from `Unit`:
the structural steps are proved by `kernel_disch`, and the symmetry is the cocommutativity of the
copy.

## Main statements

* `isReversible_comp`: Lemma 2.3.5 of the book.
* `invariant_comp`: `π` is then invariant for `S ∘ₖ R`.
* `isReversible_posterior_comp`, `invariant_posterior_comp`: the same results with the posterior
  `R†π` of Mathlib as `S`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

open scoped KernelHom

namespace ProbabilityTheory.Kernel.DataAugmentation

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Lemma 2.3.5 of Douc et al.: if `π(dx) R(x, dy) = π'(dy) S(y, dx)`, then `π` is reversible with
respect to the kernel `RS`. -/
theorem isReversible_comp (π : Measure X) [SFinite π] (π' : Measure Y) [SFinite π']
    (R : Kernel X Y) (S : Kernel Y X) [IsSFiniteKernel R] [IsSFiniteKernel S]
    (h : π ⊗ₘ R = (π' ⊗ₘ S).map Prod.swap) :
    IsReversible (S ∘ₖ R) π := by
  -- The hypothesis, with the measures seen as kernels from `Unit`.
  have hk : (Kernel.id ×ₖ R) ∘ₖ const Unit π = (S ×ₖ Kernel.id) ∘ₖ const Unit π' := by
    simp only [comp_const]
    congr 1
    rw [← Measure.compProd_eq_comp_prod, h, ← Measure.swap_comp, Measure.compProd_eq_comp_prod,
      Measure.comp_assoc, swap_prod]
  -- The computation of the book: `π ⊗ RS = ∫ S(y, ·) ⊗ S(y, ·) dπ'(y)`.
  have key : (Kernel.id ×ₖ (S ∘ₖ R)) ∘ₖ const Unit π = (S ×ₖ S) ∘ₖ const Unit π' := by
    calc (Kernel.id ×ₖ (S ∘ₖ R)) ∘ₖ const Unit π
    _ = (Kernel.id ∥ₖ S) ∘ₖ ((Kernel.id ×ₖ R) ∘ₖ const Unit π) := by kernel_disch
    _ = (Kernel.id ∥ₖ S) ∘ₖ ((S ×ₖ Kernel.id) ∘ₖ const Unit π') := by rw [hk]
    _ = (S ×ₖ S) ∘ₖ const Unit π' := by kernel_disch
  -- This measure is symmetric.
  have hs : (Kernel.id ×ₖ (S ∘ₖ R)) ∘ₖ const Unit π
      = swap X X ∘ₖ ((Kernel.id ×ₖ (S ∘ₖ R)) ∘ₖ const Unit π) := by
    calc (Kernel.id ×ₖ (S ∘ₖ R)) ∘ₖ const Unit π
    _ = (S ×ₖ S) ∘ₖ const Unit π' := key
    _ = swap X X ∘ₖ ((S ×ₖ S) ∘ₖ const Unit π') := by kernel_disch
    _ = swap X X ∘ₖ ((Kernel.id ×ₖ (S ∘ₖ R)) ∘ₖ const Unit π) := by rw [key]
  -- Back to the measure `π ⊗ RS`, evaluated on rectangles.
  have hm : π ⊗ₘ (S ∘ₖ R) = (π ⊗ₘ (S ∘ₖ R)).map Prod.swap := by
    have := congrArg (fun κ ↦ κ ()) hs
    simpa only [comp_const, const_apply, ← Measure.compProd_eq_comp_prod, Measure.swap_comp]
      using this
  intro A B hA hB
  rw [← Measure.compProd_apply_prod hA hB, hm, Measure.map_apply measurable_swap (hA.prod hB),
    Set.preimage_swap_prod, Measure.compProd_apply_prod hB hA]

/-- Under the assumptions of `isReversible_comp`, `π` is invariant for the kernel `RS`. -/
theorem invariant_comp (π : Measure X) [SFinite π] (π' : Measure Y) [SFinite π']
    (R : Kernel X Y) (S : Kernel Y X) [IsMarkovKernel R] [IsMarkovKernel S]
    (h : π ⊗ₘ R = (π' ⊗ₘ S).map Prod.swap) :
    Invariant (S ∘ₖ R) π :=
  (isReversible_comp π π' R S h).invariant

section Posterior

variable [StandardBorelSpace X] [Nonempty X]

/-- With the posterior `R†π` of Mathlib as `S`, for a probability measure `π` and a Markov kernel
`R`, the data augmentation kernel is reversible with respect to `π`. -/
theorem isReversible_posterior_comp (π : Measure X) [IsProbabilityMeasure π] (R : Kernel X Y)
    [IsMarkovKernel R] :
    IsReversible ((R†π) ∘ₖ R) π :=
  isReversible_comp π (R ∘ₘ π) R (R†π) (by
    rw [compProd_posterior_eq_map_swap, Measure.map_map measurable_swap measurable_swap,
      Prod.swap_swap_eq, Measure.map_id])

/-- The data augmentation kernel `(R†π) ∘ₖ R` leaves `π` invariant. -/
theorem invariant_posterior_comp (π : Measure X) [IsProbabilityMeasure π] (R : Kernel X Y)
    [IsMarkovKernel R] :
    Invariant ((R†π) ∘ₖ R) π :=
  (isReversible_posterior_comp π R).invariant

end Posterior

end ProbabilityTheory.Kernel.DataAugmentation
