/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import KernelHom.Tactic.Hom.KernelHom
import Mathlib.Tactic.CategoryTheory.Coherence

open Lean Elab Tactic CategoryTheory
open Lean Elab Tactic Meta CategoryTheory Parser.Tactic ProbabilityTheory MonoidalCategory


open scoped MonoidalCategory

/-!
# Kernel category tactics

This file implements the `kernel_coherence` and `kernel_monoidal` tactics, which apply the
`kernel_hom` transformation and then use categorical `coherence` or `monoidal` tactics to solve the
resulting goal.

## Main declarations

- `kernel_coherence`: tactic combining kernel_hom and categorical coherence.
- `kernel_monoidal`: tactic combining kernel_hom and categorical monoidal coherence.
-/

/-- The `kernel_coherence` tactic applies the `kernel_hom` transformation to the goal and then
invokes the `coherence` tactic to solve the resulting goal. -/
syntax "kernel_coherence" : tactic

-- ANCHOR: kernel_coherence_tactic
elab_rules : tactic
  | `(tactic| kernel_coherence) => do
    evalTactic (← `(tactic| kernel_hom))
    evalTactic (← `(tactic| coherence))
-- ANCHOR_END: kernel_coherence_tactic

/-- The `kernel_coherence` tactic applies the `kernel_hom` transformation to the goal and then
invokes the `monoidal` tactic to solve the resulting goal. -/
syntax "kernel_monoidal" : tactic

-- ANCHOR: kernel_monoidal_tactic
elab_rules : tactic
  | `(tactic| kernel_monoidal) => do
    evalTactic (← `(tactic| kernel_hom))
    evalTactic (← `(tactic| monoidal))
-- ANCHOR_END: kernel_monoidal_tactic
