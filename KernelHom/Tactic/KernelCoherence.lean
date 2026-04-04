/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import KernelHom.Tactic.Hom.KernelHom
import Mathlib.Tactic.CategoryTheory.Coherence

open Lean Elab Tactic CategoryTheory

open scoped MonoidalCategory

@[simp]
lemma CategoryTheory.tensorObjSFinker {X Y : SFinKer} :
    X ⊗ Y = SFinKer.of (X.carrier × Y.carrier) := rfl

/-- The `kernel_coherence` tactic applies the `kernel_hom` transformation to the goal and then
invokes the `coherence` tactic to solve the resulting goal. -/
elab "kernel_coherence" : tactic => do
  evalTactic (← `(tactic| kernel_hom))
  evalTactic (← `(tactic| coherence))

/-- The `kernel_coherence` tactic applies the `kernel_hom` transformation to the goal and then
invokes the `monoidal` tactic to solve the resulting goal. -/
elab "kernel_monoidal" : tactic => do
  evalTactic (← `(tactic| kernel_hom))
  evalTactic (← `(tactic| monoidal))
