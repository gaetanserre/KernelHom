/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import MeasureKernel
public import KernelHom

/-!
# Tests for Measure-Kernel
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

/-! ### `measure_kernel` on the goal and on hypotheses -/

example (μ ν : Measure X) (h : μ = ν) : ν = μ := by
  measure_kernel at h ⊢
  guard_hyp h : Kernel.const Unit μ = Kernel.const Unit ν
  guard_target = Kernel.const Unit ν = Kernel.const Unit μ
  exact h.symm

example (μ ν : Measure X) (h : μ = ν) : ν = μ := by
  measure_kernel at *
  guard_hyp h : Kernel.const Unit μ = Kernel.const Unit ν
  guard_target = Kernel.const Unit ν = Kernel.const Unit μ
  exact h.symm

/-! ### The operations on measures -/

/-- `κ ∘ₘ μ` is translated into `κ ∘ₖ Kernel.const Unit μ`, recursively. -/
example (κ : Kernel X Y) (η : Kernel Y Z) (μ : Measure X) (ν : Measure Z)
    (h : η ∘ₘ (κ ∘ₘ μ) = ν) : η ∘ₘ (κ ∘ₘ μ) = ν := by
  measure_kernel at h ⊢
  guard_target = η ∘ₖ (κ ∘ₖ Kernel.const Unit μ) = Kernel.const Unit ν
  exact h

/-- `μ ⊗ₘ κ` is translated into `(Kernel.id ×ₖ κ) ∘ₖ Kernel.const Unit μ`. -/
example (μ : Measure X) [SFinite μ] (κ : Kernel X Y) [IsSFiniteKernel κ] (ν : Measure (X × Y))
    (h : μ ⊗ₘ κ = ν) : μ ⊗ₘ κ = ν := by
  measure_kernel at h ⊢
  guard_target = (Kernel.id ×ₖ κ) ∘ₖ Kernel.const Unit μ = Kernel.const Unit ν
  exact h

/-- `μ.prod ν` is translated into `Kernel.const Unit μ ×ₖ Kernel.const Unit ν`. -/
example (μ : Measure X) [SFinite μ] (ν : Measure Y) [SFinite ν] (ρ : Measure (X × Y))
    (h : μ.prod ν = ρ) : μ.prod ν = ρ := by
  measure_kernel at h ⊢
  guard_target = Kernel.const Unit μ ×ₖ Kernel.const Unit ν = Kernel.const Unit ρ
  exact h

/-- Without s-finiteness, `μ ⊗ₘ κ` and `μ.prod ν` are translated as atoms. -/
example (μ : Measure X) (κ : Kernel X Y) (ν : Measure Y) (h : μ ⊗ₘ κ = μ.prod ν) :
    μ ⊗ₘ κ = μ.prod ν := by
  measure_kernel at h ⊢
  guard_target = Kernel.const Unit (μ ⊗ₘ κ) = Kernel.const Unit (μ.prod ν)
  exact h

/-- `Measure.map` is not translated. -/
example (μ : Measure X) (f : X → Y) (ν : Measure Y) (h : μ.map f = ν) : μ.map f = ν := by
  measure_kernel at h ⊢
  guard_target = Kernel.const Unit (μ.map f) = Kernel.const Unit ν
  exact h

/-! ### `kernel_measure` is the inverse of `measure_kernel` -/

example (κ : Kernel X Y) (η : Kernel Y Z) (μ : Measure X) (ν : Measure Z)
    (h : η ∘ₘ (κ ∘ₘ μ) = ν) : η ∘ₘ (κ ∘ₘ μ) = ν := by
  measure_kernel at h ⊢
  kernel_measure at h ⊢
  guard_hyp h : η ∘ₘ (κ ∘ₘ μ) = ν
  guard_target = η ∘ₘ (κ ∘ₘ μ) = ν
  exact h

example (μ : Measure X) [SFinite μ] (κ : Kernel X Y) [IsSFiniteKernel κ] (ν : Measure Z)
    [SFinite ν] (ρ : Measure ((X × Y) × Z)) (h : (μ ⊗ₘ κ).prod ν = ρ) :
    (μ ⊗ₘ κ).prod ν = ρ := by
  measure_kernel at h ⊢
  guard_target =
    ((Kernel.id ×ₖ κ) ∘ₖ Kernel.const Unit μ) ×ₖ Kernel.const Unit ν = Kernel.const Unit ρ
  kernel_measure at h ⊢
  guard_hyp h : (μ ⊗ₘ κ).prod ν = ρ
  guard_target = (μ ⊗ₘ κ).prod ν = ρ
  exact h

/-- `kernel_measure` also translates back the kernels obtained by rewriting. -/
example (κ : Kernel X Y) (η : Kernel Y Z) (μ : Measure X) (ν : Measure Z)
    (h : η ∘ₘ (κ ∘ₘ μ) = ν) : (η ∘ₖ κ) ∘ₘ μ = ν := by
  measure_kernel at h
  rw [← Kernel.comp_assoc] at h
  kernel_measure at h
  guard_hyp h : (η ∘ₖ κ) ∘ₘ μ = ν
  exact h

/-! ### With the tactics about kernels -/

example (κ : Kernel X Y) (η : Kernel Y Z) [IsSFiniteKernel κ] [IsSFiniteKernel η] (μ : Measure X)
    [SFinite μ] :
    η ∘ₘ (κ ∘ₘ μ) = (η ∘ₖ κ) ∘ₘ μ := by
  measure_kernel
  kernel_disch

example (κ : Kernel X Y) (η : Kernel X Z) [IsSFiniteKernel κ] [IsSFiniteKernel η] (μ : Measure X)
    [SFinite μ] :
    Kernel.swap Y Z ∘ₘ ((κ ×ₖ η) ∘ₘ μ) = (η ×ₖ κ) ∘ₘ μ := by
  measure_kernel
  kernel_disch

/-- Parallel kernels act on the factors of a product of measures. -/
example (κ : Kernel X Z) (η : Kernel Y Z) [IsSFiniteKernel κ] [IsSFiniteKernel η] (μ : Measure X)
    [SFinite μ] (ν : Measure Y) [SFinite ν] :
    (κ ∥ₖ η) ∘ₘ μ.prod ν = (κ ∘ₘ μ).prod (η ∘ₘ ν) := by
  measure_kernel
  kernel_disch

/-- The commutativity of the product of measures. -/
example (μ : Measure X) [SFinite μ] (ν : Measure Y) [SFinite ν] :
    Kernel.swap X Y ∘ₘ μ.prod ν = ν.prod μ := by
  measure_kernel
  kernel_disch

/-! ### Failures -/

/-- `measure_kernel` only applies to equalities of measures. -/
example (κ η : Kernel X Y) (h : κ = η) : κ = η := by
  fail_if_success measure_kernel
  exact h

/-- `kernel_measure` only recognizes the kernels built by `measure_kernel`. -/
example (κ η : Kernel Unit X) (h : κ = η) : κ = η := by
  fail_if_success kernel_measure
  exact h
