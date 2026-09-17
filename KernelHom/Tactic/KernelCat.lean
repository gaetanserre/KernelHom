/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import KernelHom.ForMathlib.Comon
public import KernelHom.Tactic.KernelHom
public import Mathlib.Tactic.CategoryTheory.Coherence

/-!
# Kernel category tactics

This file implements tactics which apply the `kernel_hom` transformation and then use a
categorical tactic to solve the resulting goal.

## Main declarations

* `kernel_disch`: `kernel_hom` followed by `cat_disch` or `monoidal`, possibly after normalizing the
  tensor products of morphisms. It is the tactic to use by default.
* `kernel_monoidal`: `kernel_hom` followed by `monoidal`.
* `kernel_coherence`: `kernel_hom` followed by `coherence`.
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
tries to solve the resulting goal with:
1. `cat_disch`;
2. `monoidal`;
3. `cat_disch`, after merging the whiskers and the compositions of tensor products into single
  tensor products, together with the counit and comultiplication laws of the comonoid structure
  and of the deterministic and Markov kernels. This handles the exchange law and the laws hidden in
  tensor products;
4. `monoidal`, after splitting the tensor products of compositions and applying the
  coassociativity of the comultiplication.

As it tries both `cat_disch` and `monoidal`, it is the tactic to use by default. -/
syntax (name := kernelDisch) "kernel_disch" : tactic

elab_rules : tactic
  | `(tactic| kernel_disch) => do
    evalTactic (← `(tactic| kernel_hom))
    evalTactic (← `(tactic| first
      | cat_disch
      | (monoidal; done)
      | ((try simp only [← MonoidalCategory.tensorHom_id, ← MonoidalCategory.id_tensorHom,
          MonoidalCategory.tensorHom_comp_tensorHom,
          MonoidalCategory.tensorHom_comp_tensorHom_assoc,
          Category.id_comp, Category.comp_id, Category.assoc,
          IsComonHom.hom_comul, IsComonHom.hom_comul_assoc,
          IsComonHom.hom_counit, IsComonHom.hom_counit_assoc,
          Kernel.hom_counit_of_isMarkovKernel, Kernel.hom_counit_of_isMarkovKernel_assoc,
          ComonObj.comul_counit_hom, ComonObj.comul_counit_hom_assoc,
          ComonObj.counit_comul_hom, ComonObj.counit_comul_hom_assoc,
          ComonObj.comul_tensorHom_counit_comp, ComonObj.comul_tensorHom_counit_comp_assoc,
          ComonObj.comul_counit_comp_tensorHom, ComonObj.comul_counit_comp_tensorHom_assoc])
        <;> cat_disch)
      | (((try simp only [← MonoidalCategory.whiskerRight_comp_tensorHom,
          ← MonoidalCategory.whiskerLeft_comp_tensorHom, Category.assoc,
          ComonObj.comul_assoc, ComonObj.comul_assoc_assoc])
        <;> monoidal); done)
      ))

/-- The `aesop_kernel` tactic applies the `kernel_hom` transformation to the goal and then
invokes `aesop` with the `CategoryTheory` rule set, using the same configuration as `aesop_cat`. -/
syntax (name := aesopKernel) "aesop_kernel" : tactic

elab_rules : tactic
  | `(tactic| aesop_kernel) => do
    evalTactic (← `(tactic| kernel_hom))
    evalTactic (← `(tactic| aesop
      (config := { introsTransparency? := some .default, terminal := true })
      (rule_sets := [$(Lean.mkIdent `CategoryTheory):ident])))
