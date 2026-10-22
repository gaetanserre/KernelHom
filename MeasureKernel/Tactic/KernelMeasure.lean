/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import MeasureKernel.Tactic.MeasureKernel

/-!
# `kernel_measure` tactic

This file implements the `kernel_measure` tactic, the inverse of `measure_kernel`.
It transforms equalities of kernels from `Unit` back into
equivalent equalities of measures.

## Main declarations

* `kernelToMeasure`: recursive translation from kernel expressions to measure expressions.
* `MeasureEquality`: core implementation of `kernel_measure` on an equality.
* `kernel_measure`: user-facing tactic (with location support).
-/

public meta section

open Lean Elab Tactic Meta Qq Parser.Tactic MeasureTheory ProbabilityTheory

namespace MeasureKernel

/-- The measure `e'` of a proof `pf : e = Kernel.const Unit e'`, with the proof. -/
def withMeasureOfProof (pf : Expr) : MetaM (Expr × Expr) := do
  let some (_, _, rhs) := (← inferType pf).eq? | throwError "Expected an equality, got: {pf}."
  let_expr Kernel.const _ _ _ _ μ := rhs | throwError "Expected a constant kernel, got: {rhs}."
  return (μ, pf)

/-- The kernel `κ` of `Kernel.id ×ₖ κ`, if `e` has this form. -/
def idProd? (e : Expr) : Option Expr := do
  let_expr Kernel.prod _ _ _ _ _ _ id κ := e | none
  if id.isAppOf ``Kernel.id then some κ else none

/-- Recursive translation of a kernel `e : Kernel Unit X` into a measure `e'`. Returns `e'` together
with a proof of `e = Kernel.const Unit e'`. Each step is a single application of a translation
lemma, given the translations of the subterms (`Kernel.comp_const_of_eq`, ...). Only the kernels
built by `measure_kernel` are recognized. -/
partial def kernelToMeasure (e : Expr) : MetaM (Expr × Expr) := do
  match_expr e with
  | Kernel.const α _ _ _ μ =>
    unless α.isConstOf ``Unit do throwError "Expected a constant kernel from `Unit`, got: {e}."
    return (μ, ← mkEqRefl e)
  | Kernel.comp _ _ _ _ _ _ η K =>
    let (_, pK) ← kernelToMeasure K
    if let some κ := idProd? η then
      try return ← withMeasureOfProof (← mkAppM ``Kernel.id_prod_comp_const_of_eq #[κ, pK])
      catch _ => pure ()
    withMeasureOfProof (← mkAppM ``Kernel.comp_const_of_eq #[η, pK])
  | Kernel.prod _ _ _ _ _ _ K L =>
    let (_, pK) ← kernelToMeasure K
    let (_, pL) ← kernelToMeasure L
    withMeasureOfProof (← mkAppM ``Kernel.prod_const_of_eq #[pK, pL])
  | _ => throwError "Expected a kernel built by `measure_kernel`, got: {e}."

/-- Transform an equality of kernels from `Unit` into an equivalent equality of measures, along
with a proof of equivalence. -/
def MeasureEquality (eq : Expr) : MetaM (Expr × Expr) := do
  let some (_, lhs, rhs) := eq.eq? | throwError "Expected an equality, got: {eq}."
  let (μ, pμ) ← kernelToMeasure lhs
  let (ν, pν) ← kernelToMeasure rhs
  let pf ← mkAppM ``Kernel.const_congr_of_eq #[pμ, pν]
  return (← mkEq μ ν, ← mkEqSymm pf)

/-- The `kernel_measure` tactic is the inverse of `measure_kernel`: it transforms an
equality of kernels from `Unit` back to an equivalent equality of
measures.

The tactic supports location specifiers like `rw` or `simp`:
- `kernel_measure` — applies to the goal
- `kernel_measure at h` — applies to hypothesis `h`
- `kernel_measure at h₁ h₂` — applies to multiple hypotheses
- `kernel_measure at h ⊢` — applies to hypothesis `h` and the goal
- `kernel_measure at *` — applies to all hypotheses and the goal

It is useful to switch back to measure equations once kernel rewrites are done. -/
syntax (name := kernelMeasure) "kernel_measure" (ppSpace location)? : tactic

elab_rules : tactic
  | `(tactic| kernel_measure $[$loc]?) =>
    applyLocTactic (expandOptLocation <| mkOptionalNode loc) MeasureEquality

end MeasureKernel
