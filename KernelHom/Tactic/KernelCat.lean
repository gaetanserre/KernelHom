/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import KernelHom.Tactic.KernelHom
public import Mathlib.Tactic.CategoryTheory.Coherence

/-!
# Kernel category tactics

This file implements tactics which apply the `kernel_hom` transformation and then use a
categorical tactic to solve the resulting goal.

## Main declarations

* `kernel_monoidal`: `kernel_hom` followed by `monoidal`.
* `kernel_coherence`: `kernel_hom` followed by `coherence`.
* `kernel_disch`: `kernel_hom` followed by `cat_disch`.
* `aesop_kernel`: `kernel_hom` followed by `aesop` with the `CategoryTheory` rule set, skipping the
  `rfl_cat` attempt of `cat_disch`.
-/

public meta section

open Lean Elab Tactic CategoryTheory
open Lean Elab Tactic Meta CategoryTheory Parser.Tactic ProbabilityTheory MonoidalCategory


/-- The `kernel_monoidal` tactic applies the `kernel_hom` transformation to the goal and then
invokes the `monoidal` tactic to solve or simplify the resulting goal. -/
syntax (name := kernelMonoidal) "kernel_monoidal" : tactic

elab_rules : tactic
  | `(tactic| kernel_monoidal) => do
    evalTactic (← `(tactic| kernel_hom))
    evalTactic (← `(tactic| monoidal))

/-- The `kernel_coherence` tactic applies the `kernel_hom` transformation to the goal and then
invokes the `coherence` tactic to solve the resulting goal. -/
syntax (name := kernelCoherence) "kernel_coherence" : tactic

elab_rules : tactic
  | `(tactic| kernel_coherence) => do
    evalTactic (← `(tactic| kernel_hom))
    evalTactic (← `(tactic| coherence))

/-- The `kernel_disch` tactic applies the `kernel_hom` transformation to the goal and then
invokes the `cat_disch` tactic to solve the resulting goal. -/
syntax (name := kernelDisch) "kernel_disch" : tactic

elab_rules : tactic
  | `(tactic| kernel_disch) => do
    evalTactic (← `(tactic| kernel_hom))
    evalTactic (← `(tactic| cat_disch))

/-- The `aesop_kernel` tactic applies the `kernel_hom` transformation to the goal and then
invokes `aesop` with the `CategoryTheory` rule set, using the same configuration as `aesop_cat`. -/
syntax (name := aesopKernel) "aesop_kernel" : tactic

elab_rules : tactic
  | `(tactic| aesop_kernel) => do
    evalTactic (← `(tactic| kernel_hom))
    evalTactic (← `(tactic| aesop
      (config := { introsTransparency? := some .default, terminal := true })
      (rule_sets := [$(Lean.mkIdent `CategoryTheory):ident])))
