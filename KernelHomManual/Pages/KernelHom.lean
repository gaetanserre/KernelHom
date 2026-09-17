/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import KernelHom.Tactic.KernelHom
import VersoManual

open Verso.Genre Manual Verso.Genre.Manual.InlineLean Verso.Code.External

set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "kernel\\_hom tactic" =>
%%%
htmlSplit := .never
%%%

The {name kernelHom}`kernel_hom` tactic transforms a s-finite kernel equality into an equality in the {name SFinKer}`SFinKer` category, where any categorical reasoning can be applied to simplify it. For example, given kernels `κ : Kernel X Y`, `η : Kernel Y Z` and `ξ : Kernel X Z`, the following kernel equality: `η ∘ₖ κ = ξ` is transformed to `κ.hom ≫ η.hom = ξ.hom` in the {name SFinKer}`SFinKer` category, where {name ProbabilityTheory.Kernel.hom}`hom` is the translation of kernels to morphisms in {name SFinKer}`SFinKer`.

{docstring kernelHom}

The tactic can be described in 4 steps:

1. First, the derived operations `κ ×ₖ η` and `κ ⊗ₖ η` are unfolded into compositions, parallel compositions and copies ({name unfoldKernelOp}`unfoldKernelOp`).

1. Then, the equality is lifted to a common universe level with the machinery of {name EqLift}`lift_eq`, together with a proof of equivalence. When the tactic is applied at several locations, all the equalities are lifted to the same universe level, so that the translated equalities live in the same category and can be used to rewrite each other.

1. Next, it recursively traverses the lifted equality and creates a new expression where each kernel is replaced by its translation in the {name SFinKer}`SFinKer` category. The kernel operations are translated to the corresponding categorical operations (composition, tensor product, whiskers, identity, unitors, associators, braiding, copy and discard), and the other kernels `κ` to `κ.hom`. Each translated subexpression comes with a proof that it is the translation of the original one, built by congruence from the translation lemmas. This is done using the {name transformKernelToHom}`transformKernelToHom` function.

  {docstring transformKernelToHom}

1. Finally, the proofs of the two sides give, with {name ProbabilityTheory.Kernel.hom_congr}`hom_congr`, a proof that the lifted equality is equivalent to the categorical one, which replaces the goal or the hypothesis.
