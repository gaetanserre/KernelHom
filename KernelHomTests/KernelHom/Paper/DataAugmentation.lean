/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import KernelHom
public import MeasureKernel
public import Mathlib.Probability.Kernel.Posterior
public import Mathlib.Probability.Kernel.Invariance

/-!
# Reversibility of data augmentation

This file formalizes Lemma 2.3.5 of *Markov Chains*, R. Douc et al., Springer, 2018. A data
augmentation algorithm writes a probability measure `π` on `X` as the marginal of `π ⊗ R` on `X ×
Y`, where `R : Kernel X Y`. The disintegration of `π ⊗ R` along `Y` gives a kernel `S : Kernel Y X`
and a probability measure `π̃` on `Y` such that `π(dx) R(x, dy) = S(y, dx) π̃(dy)` (equation (2.3.
11) of the book). In Mathlib, `S` is the posterior `R†π` and `π̃` is `R ∘ₘ π`. The algorithm draws
`y` from `R(x)`, then `x` from `S(y)`, so that the sequence of the `x` is a Markov chain with
kernel `RS`, written `S ∘ₖ R` in Mathlib. The lemma states that `π` is reversible with respect to
this kernel.

The proof of the book computes `(π ⊗ RS)(A × B) = ∫ S(y, A) S(y, B) π̃(dy)`, which is symmetric in
`A` and `B`. The proof below follows the same steps on the measures. By Definition 1.5.1 of the book
(`isReversible_of_map_swap`), it shows that the measure `π ⊗ RS` is invariant by the swap of the
coordinates. Its structural steps are proved by `measure_kernel`, which sees the measures as
kernels from `Unit`, followed by `kernel_disch`. The symmetry is the cocommutativity of the copy.

## References

* R. Douc, E. Moulines, P. Priouret and P. Soulier, *Markov Chains*, Springer, 2018.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

open scoped KernelHom

namespace ProbabilityTheory.Kernel.DataAugmentation

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Definition 1.5.1 of Douc et al.: if the measure `π ⊗ κ` on `X × X` is symmetric, then `π` is
reversible with respect to `κ`. -/
lemma isReversible_of_map_swap {π : Measure X} [SFinite π] {κ : Kernel X X} [IsSFiniteKernel κ]
    (h : (π ⊗ₘ κ).map Prod.swap = π ⊗ₘ κ) :
    IsReversible κ π := by
  intro A B hA hB
  rw [← Measure.compProd_apply_prod hA hB, ← h, Measure.map_apply measurable_swap (hA.prod hB),
    Set.preimage_swap_prod, Measure.compProd_apply_prod hB hA]

/-- Lemma 2.3.5 of Douc et al.: the distribution `π` is reversible with respect to the kernel `RS`,
where `S = R†π`. -/
theorem isReversible_comp [StandardBorelSpace X] [Nonempty X] (π : Measure X)
    [IsProbabilityMeasure π] (R : Kernel X Y) [IsMarkovKernel R] :
    IsReversible ((R†π) ∘ₖ R) π := by
  -- By Definition 1.5.1, the measure `π ⊗ RS` on `X × X` must be symmetric.
  apply isReversible_of_map_swap
  -- Equation (2.3.11) of the book: `π(dx) R(x, dy) = S(y, dx) π̃(dy)`.
  have h : π ⊗ₘ R = swap Y X ∘ₘ ((R ∘ₘ π) ⊗ₘ R†π) := by
    rw [compProd_posterior_eq_swap_comp]
    measure_kernel
    kernel_disch
  -- The computation of the book: `π ⊗ RS = ∫ S(y, ·) ⊗ S(y, ·) π̃(dy)`.
  have key : π ⊗ₘ ((R†π) ∘ₖ R) = ((R†π) ×ₖ (R†π)) ∘ₘ (R ∘ₘ π) := by
    calc π ⊗ₘ ((R†π) ∘ₖ R)
    _ = (Kernel.id ∥ₖ R†π) ∘ₘ (π ⊗ₘ R) := by measure_kernel; kernel_disch
    _ = (Kernel.id ∥ₖ R†π) ∘ₘ (swap Y X ∘ₘ ((R ∘ₘ π) ⊗ₘ R†π)) := by rw [h]
    _ = ((R†π) ×ₖ (R†π)) ∘ₘ (R ∘ₘ π) := by measure_kernel; kernel_disch
  -- This measure is symmetric.
  rw [← Measure.swap_comp, key]
  measure_kernel
  kernel_disch

end ProbabilityTheory.Kernel.DataAugmentation
