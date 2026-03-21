/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import LeanStoch.Tactic.Quiver.KernelQuiver
import Mathlib.Tactic.CategoryTheory.Coherence

open Lean Elab Tactic CategoryTheory

elab "kernel_coherence" : tactic => do
  evalTactic (← `(tactic| kernel_quiver))
  evalTactic (← `(tactic| coherence))

elab "kernel_monoidal" : tactic => do
  evalTactic (← `(tactic| kernel_quiver))
  evalTactic (← `(tactic| monoidal))
  evalTactic (← `(tactic| try simp [MonoidalCategory.tensorObj]))
  evalTactic (← `(tactic| try simp))
