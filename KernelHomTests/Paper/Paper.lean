/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import KernelHom

/-!
# The listings of the paper

This file checks the listings of the paper *Categorical reasoning for probability kernels in
Mathlib* that are not already in `KernelHomTests/Examples.lean`, and the goals displayed in the
paper, with `#guard_msgs`. It also tests, with `fail_if_success`, the
limitations described in the paper. The declarations are in the namespace `Paper`, so that they do
not clash with those of the other test files.

## Map from the paper to the artifact

* `SFinKer` is a copy-discard category: `CopyDiscardCategory SFinKer`, in Mathlib,
  `Probability/Kernel/Category/SFinKer.lean`.
* Wide subcategories inherit the structures: `CopyDiscardCategory (WideSubcategory P)`, in Mathlib,
  `CategoryTheory/CopyDiscardCategory/Widesubcategory.lean`.
* `Stoch` is a positive Markov category: `PositiveCategory Stoch`, in Mathlib,
  `Probability/Kernel/Category/Stoch.lean`.
* Deterministic kernels: `IsDeterministic`, `isDeterministic_iff_isZeroOneMeasure`,
  `IsDeterministic.exists_eq_deterministic`, in Mathlib, `Probability/Kernel/Deterministic.lean`.
* The lifting and its compatibility lemmas: `Kernel.lift`, `Kernel.lift_congr`, ..., and their
  variants with hypotheses used by the tactics, `Kernel.lift_congr_of_eq`, `Kernel.comp_lift_of_eq`,
  ..., in Eq-Lift, `EqLift/Kernel/Lift.lean`.
* `lift_eq` and `unlift_eq`: in Eq-Lift, `EqLift/Tactic/Lift.lean` and `EqLift/Tactic/Unlift.lean`.
* The translation `Kernel.toHom`, `Kernel.toHom_congr` and the dictionary of Table 1, with the
  variants used by the tactics (`Kernel.toHom_congr_of_eq`, `Kernel.comp_toHom_of_eq`, ...): in
  Kernel-Hom, `KernelHom/Kernel/Hom.lean`; the folding of `×ₖ` and `⊗ₖ` by `hom_kernel`:
  `foldKernelOp`, in `KernelHom/Tactic/Utils.lean`, with the lemmas of
  `KernelHom/ForMathlib/Kernel.lean`.
* `kernel_hom` and `hom_kernel`: in Kernel-Hom, `KernelHom/Tactic/KernelHom.lean` and
  `KernelHom/Tactic/HomKernel.lean`.
* `kernel_disch`, `kernel_monoidal`, `kernel_coherence`, `aesop_kernel`: in Kernel-Hom,
  `KernelHom/Tactic/KernelCat.lean`.
* `#kernel_diagram`: in Kernel-Hom, `KernelHom/Tactic/KernelDiagram.lean`.
* `@[kernel_reassoc]` and `kernel_reassoc_of%`: in Kernel-Hom, `KernelHom/Tactic/Reassoc.lean`.
* The examples of Section 5 and the limitations of Section 7: this file.
* Table 2 (scope): `KernelHomTests/Examples.lean` and `KernelHomTests/Paper/Scope.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory CategoryTheory MonoidalCategory ComonObj

open scoped KernelHom

namespace ProbabilityTheory.Kernel.Paper

/-! ### Section 5.2: the goals displayed in the paper -/

/--
trace: X : Type u_1
Y : Type u_2
Z : Type u_3
inst✝⁴ : MeasurableSpace X
inst✝³ : MeasurableSpace Y
inst✝² : MeasurableSpace Z
κ : Kernel X Y
inst✝¹ : IsSFiniteKernel κ
η : Kernel X Z
inst✝ : IsSFiniteKernel η
⊢ (Δ ≫ (κ ⊗ₘ η)) ≫ (β_ Y Z).hom = Δ ≫ (η ⊗ₘ κ)
-/
#guard_msgs in
lemma swap_prod₀ {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    {κ : Kernel X Y} [IsSFiniteKernel κ] {η : Kernel X Z} [IsSFiniteKernel η] :
    swap Y Z ∘ₖ (κ ×ₖ η) = η ×ₖ κ := by
  kernel_hom
  trace_state
  cat_disch

/--
trace: X : Type u_1
Y : Type u_2
Z : Type u_3
inst✝³ : MeasurableSpace X
inst✝² : MeasurableSpace Y
inst✝¹ : MeasurableSpace Z
κ : Kernel Y Z
inst✝ : IsSFiniteKernel κ
f : X → Y
hf : Measurable f
⊢ deterministic f hf ≫ κ ≫ Δ ≫ (β_ Z Z).hom = κ.comap f hf ≫ Δ
---
trace: X : Type u_1
Y : Type u_2
Z : Type u_3
inst✝³ : MeasurableSpace X
inst✝² : MeasurableSpace Y
inst✝¹ : MeasurableSpace Z
κ : Kernel Y Z
inst✝ : IsSFiniteKernel κ
f : X → Y
hf : Measurable f
⊢ copy Z ∘ₖ κ ∘ₖ deterministic f hf = copy Z ∘ₖ κ.comap f hf
-/
#guard_msgs in
example {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (κ : Kernel Y Z) [IsSFiniteKernel κ] (f : X → Y) (hf : Measurable f) :
    swap Z Z ∘ₖ copy Z ∘ₖ κ ∘ₖ deterministic f hf =
      copy Z ∘ₖ κ.comap f hf := by
  kernel_hom
  trace_state
  simp only [IsCommComonObj.comul_comm]
  hom_kernel
  trace_state
  rw [Kernel.comp_assoc, Kernel.comp_deterministic_eq_comap]

/-! ### Section 5.4: the diagram of `swap_prod₀` (drawn in the infoview) -/

set_option linter.hashCommand false in
#kernel_diagram swap_prod₀

/-! ### Section 5.5: `@[kernel_reassoc]` and `kernel_reassoc_of%` -/

section Reassoc

variable {X Y Z W Y' Z' : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  [MeasurableSpace W] [MeasurableSpace Y'] [MeasurableSpace Z']
  (κ : Kernel X Y) [IsSFiniteKernel κ] (η : Kernel Y Z) [IsSFiniteKernel η]
  (κ' : Kernel X Y') [IsSFiniteKernel κ'] (η' : Kernel Y' Z') [IsSFiniteKernel η']

@[kernel_reassoc]
lemma parallelComp_comp_prod₀ :
    (η ∥ₖ η') ∘ₖ (κ ×ₖ κ') = (η ∘ₖ κ) ×ₖ (η' ∘ₖ κ') := by
  kernel_disch

variable (ξ : Kernel (Z × Z') W) [IsSFiniteKernel ξ]

/--
info: parallelComp_comp_prod₀_assoc κ η κ' η' ξ :
  ξ ∘ₖ (η ∥ₖ η') ∘ₖ (κ ×ₖ κ') = ξ ∘ₖ (η ∘ₖ κ ×ₖ (η' ∘ₖ κ'))
-/
#guard_msgs (whitespace := lax) in
#check parallelComp_comp_prod₀_assoc κ η κ' η' ξ

/-- The products of the generated lemma are folded back (Section 5.5), so that it rewrites a goal
written with `×ₖ`, as does `kernel_reassoc_of%`. -/
example : ξ ∘ₖ (η ∥ₖ η') ∘ₖ (κ ×ₖ κ') = ξ ∘ₖ ((η ∘ₖ κ) ×ₖ (η' ∘ₖ κ')) := by
  rw [parallelComp_comp_prod₀_assoc]

example : ξ ∘ₖ (η ∥ₖ η') ∘ₖ (κ ×ₖ κ') = ξ ∘ₖ ((η ∘ₖ κ) ×ₖ (η' ∘ₖ κ')) := by
  rw [kernel_reassoc_of% parallelComp_comp_prod₀ κ η κ' η']

end Reassoc

example {X Y Z W : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    [MeasurableSpace W] (κ : Kernel X Y) (η : Kernel Y Z) (ζ : Kernel X Z) (ξ : Kernel Z W)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] [IsSFiniteKernel ζ] [IsSFiniteKernel ξ]
    (h : η ∘ₖ κ = ζ) : ξ ∘ₖ η ∘ₖ κ = ξ ∘ₖ ζ := by
  rw [kernel_reassoc_of% h]

/-! ### Section 7: limitations -/

section Limitations

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

/-- The marginals are not translated. -/
example (κ : Kernel X Y) [IsSFiniteKernel κ] (η : Kernel X Z) [IsMarkovKernel η] :
    fst (κ ×ₖ η) = κ := by
  fail_if_success kernel_disch
  exact fst_prod κ η

/-- The inverse unitors are only recognized by `hom_kernel`. -/
example (κ : Kernel Z Y) [IsSFiniteKernel κ] :
    (Kernel.discard.{_, 0} Z ∥ₖ κ) ∘ₖ Kernel.copy Z = (Kernel.id.map fun x ↦ ((), x)) ∘ₖ κ := by
  fail_if_success kernel_disch
  kernel_hom
  simp only [ComonObj.counit_comul_hom]
  hom_kernel
  rfl

end Limitations

end ProbabilityTheory.Kernel.Paper
