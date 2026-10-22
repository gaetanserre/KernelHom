/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import MeasureKernel.Measure.Const
public import EqLift.Tactic.Location
public import Lean.Elab.Tactic.Location
public meta import Qq

/-!
# `measure_kernel` tactic

This file implements the `measure_kernel` tactic, which transforms equalities of
measures into equivalent equalities of kernels from `Unit`.

The translation sends a measure `μ` to its constant kernel `Kernel.const Unit μ`, and the operations
on measures to operations on kernels:

| Measure       | Kernel                  | Lemma                             |
|---------------|-------------------------|-----------------------------------|
| `κ ∘ₘ μ`      | `κ ∘ₖ K`                | `Kernel.comp_const_of_eq`         |
| `μ ⊗ₘ κ`      | `(Kernel.id ×ₖ κ) ∘ₖ K` | `Kernel.id_prod_comp_const_of_eq` |
| `μ.prod ν`    | `K ×ₖ L`                | `Kernel.prod_const_of_eq`         |
| any other `μ` | `Kernel.const Unit μ`   | reflexivity                       |

where `K` and `L` are the translations of `μ` and `ν`. The translations of `⊗ₘ` and `Measure.prod`
need the measures and the kernel to be s-finite; otherwise, the measure is translated as an atom.
`Measure.map` is not translated.

## Main declarations

* `measureToKernel`: recursive translation from measure expressions to kernel expressions.
* `KernelEquality`: core implementation of `measure_kernel` on an equality.
* `measure_kernel`: user-facing tactic (with location support).
-/

public meta section

open Lean Elab Tactic Meta Qq Parser.Tactic MeasureTheory ProbabilityTheory

namespace MeasureKernel

/-- The universe level, the carrier and the measurable space of the type `Measure X` of `μ`. -/
def measureCarrier (μ : Expr) : MetaM ((u : Level) × (X : Q(Type u)) × Q(MeasurableSpace $X)) := do
  let T ← whnfR (← inferType μ)
  let_expr MeasureTheory.Measure X mX := T | throwError "Expected a measure, got: {μ}."
  let u ← getDecLevel X
  return ⟨u, X, mX⟩

/-- Translation of a measure `e : Measure X` as an atom: `Kernel.const Unit e`, with a proof by
reflexivity. -/
def atomToKernel (e : Expr) : MetaM (Expr × Expr) := do
  let ⟨_, X, _⟩ ← measureCarrier e
  have e : Q(Measure $X) := e
  have κ : Q(Kernel Unit $X) := q(Kernel.const Unit $e)
  return (κ, q(Eq.refl $κ))

/-- The left-hand side `e'` of a proof `pf : e' = Kernel.const Unit e`, with the proof. -/
def withKernelOfProof (pf : Expr) : MetaM (Expr × Expr) := do
  let some (_, lhs, _) := (← inferType pf).eq? | throwError "Expected an equality, got: {pf}."
  return (lhs, pf)

/-- Recursive translation of a measure `e : Measure X` into a kernel `e' : Kernel Unit X`. Returns
`e'` together with a proof of `e' = Kernel.const Unit e`. Each step is a single application of a
translation lemma, given the translations of the subterms (`Kernel.comp_const_of_eq`, ...). A
measure that is not built from the operations of the table above, or whose instances cannot be
found, is translated as an atom. -/
partial def measureToKernel (e : Expr) : MetaM (Expr × Expr) := do
  match_expr e with
  | MeasureTheory.Measure.bind _ _ _ _ μ f =>
    let_expr DFunLike.coe _ _ _ _ κ := f | atomToKernel e
    let (_, pK) ← measureToKernel μ
    withKernelOfProof (← mkAppM ``Kernel.comp_const_of_eq #[κ, pK])
  | MeasureTheory.Measure.compProd _ _ _ _ μ κ =>
    try
      let (_, pK) ← measureToKernel μ
      withKernelOfProof (← mkAppM ``Kernel.id_prod_comp_const_of_eq #[κ, pK])
    catch _ => atomToKernel e
  | MeasureTheory.Measure.prod _ _ _ _ μ ν =>
    try
      let (_, pK) ← measureToKernel μ
      let (_, pL) ← measureToKernel ν
      withKernelOfProof (← mkAppM ``Kernel.prod_const_of_eq #[pK, pL])
    catch _ => atomToKernel e
  | _ => atomToKernel e

/-- Transform an equality of measures into an equivalent equality of kernels from `Unit`, along with
a proof of equivalence. -/
def KernelEquality (eq : Expr) : MetaM (Expr × Expr) := do
  let eq ← whnfR (← instantiateMVars eq)
  let some (_, lhs, rhs) := eq.eq? | throwError "Expected an equality, got: {eq}."
  let (κ, pκ) ← measureToKernel lhs
  let (η, pη) ← measureToKernel rhs
  return (← mkEq κ η, ← mkAppM ``Kernel.const_congr_of_eq #[pκ, pη])

/-- The `measure_kernel` tactic transforms a measure equality to an equivalent equality of
kernels from `Unit`.

The tactic supports location specifiers like `rw` or `simp`:
* `measure_kernel` — applies to the goal
* `measure_kernel at h` — applies to hypothesis `h`
* `measure_kernel at h₁ h₂` — applies to multiple hypotheses
* `measure_kernel at h ⊢` — applies to hypothesis `h` and the goal
* `measure_kernel at *` — applies to all hypotheses and the goal

Example:
```lean
example {X : Type*} [MeasurableSpace X] (μ ν : Measure X) (h : μ = ν) : ν = μ := by
  measure_kernel at h ⊢
  exact h.symm
``` -/
syntax (name := measureKernel) "measure_kernel" (ppSpace location)? : tactic

elab_rules : tactic
  | `(tactic| measure_kernel $[$loc]?) =>
    applyLocTactic (expandOptLocation <| mkOptionalNode loc) KernelEquality

end MeasureKernel
