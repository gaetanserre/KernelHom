/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import KernelHom.Tactic.HomKernel
import VersoManual

open Verso.Genre Manual Verso.Genre.Manual.InlineLean Verso.Code.External

set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "hom\\_kernel tactic" =>
%%%
htmlSplit := .never
%%%

The {name homKernel}`hom_kernel` tactic is the inverse of {name kernelHom}`kernel_hom`. It transforms categorical equalities in the {name SFinKer}`SFinKer` category back into equivalent kernel equalities. For example, given morphisms `κ.toHom ≫ η.toHom = ξ.toHom` in the {name SFinKer}`SFinKer` category, the tactic transforms it back to the kernel equality `η ∘ₖ κ = ξ`.

{docstring homKernel}

The tactic can be described in 4 steps:

1. First, it recursively traverses the categorical equality and creates a new expression where each morphism is replaced by its kernel counterpart: the categorical operations (composition, tensor product, whiskers, identity, unitors, associators, braiding, copy and discard) are translated to the corresponding kernel operations, and `κ.toHom` to `κ`. As for {name kernelHom}`kernel_hom`, each translated subexpression comes with a proof given by the same congruence lemmas. This is done using the {name homToKernel}`homToKernel` function.

  {docstring homToKernel}

1. Then, the resulting equality of lifted kernels is un-lifted to the original universe levels of the carrier spaces with the machinery of {name EqUnlift}`unlift_eq`.

1. The products `×ₖ` and composition-products `⊗ₖ`, which {name kernelHom}`kernel_hom` unfolds into copies, parallel compositions and structural kernels, are folded back by the function {name foldKernelOp}`foldKernelOp`. As the compositions of kernels associate to the left, a product preceded by a kernel `ξ` reads `ξ ∘ₖ (κ ∥ₖ η) ∘ₖ copy X`, which does not contain the unfolding `(κ ∥ₖ η) ∘ₖ copy X` of `κ ×ₖ η` as a subterm. Each operation is therefore folded by two lemmas, with and without such a prefix, such as {name ProbabilityTheory.Kernel.comp_parallelComp_comp_copy_eq_comp_prod}`comp_parallelComp_comp_copy_eq_comp_prod` and {name ProbabilityTheory.Kernel.parallelComp_comp_copy}`parallelComp_comp_copy` for `×ₖ`. A product written unfolded in the original equality is folded as well.

  {docstring foldKernelOp}

1. Finally, the proofs are combined, with {name ProbabilityTheory.Kernel.toHom_congr_of_eq}`toHom_congr_of_eq`, into a proof that the categorical equality is equivalent to the kernel equality, which replaces the goal or the hypothesis.

Note that when `PUnit` is encountered during the un-lifting process, it un-lifts to `Unit`, no matter the universe level of the original `PUnit` carrier. This is because `PUnit` is used as the unit object of the monoidal structure, which makes it hard to recover the original universe level.
