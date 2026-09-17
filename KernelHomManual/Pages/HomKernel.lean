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

The {name homKernel}`hom_kernel` tactic is the inverse of {name kernelHom}`kernel_hom`. It transforms categorical equalities in the {name SFinKer}`SFinKer` category back into equivalent kernel equalities. For example, given morphisms `κ.hom ≫ η.hom = ξ.hom` in the {name SFinKer}`SFinKer` category, the tactic transforms it back to the kernel equality `η ∘ₖ κ = ξ`.

{docstring homKernel}

The tactic can be described in 3 steps:

1. First, it recursively traverses the categorical equality and creates a new expression where each morphism is replaced by its kernel counterpart: the categorical operations (composition, tensor product, whiskers, identity, unitors, associators, braiding, copy and discard) are translated to the corresponding kernel operations, and `κ.hom` to `κ`. As for {name kernelHom}`kernel_hom`, each translated subexpression comes with a proof built by congruence. This is done using the {name transformHomToKernel}`transformHomToKernel` function.

  {docstring transformHomToKernel}

1. Then, the resulting equality of lifted kernels is un-lifted to the original universe levels of the carrier spaces with the machinery of {name EqUnlift}`unlift_eq`.

1. Finally, the proofs are combined, with {name ProbabilityTheory.Kernel.hom_congr}`hom_congr`, into a proof that the categorical equality is equivalent to the kernel equality, which replaces the goal or the hypothesis.

Note that when `PUnit` is encountered during the un-lifting process, it un-lifts to `Unit`, no matter the universe level of the original `PUnit` carrier. This is because `PUnit` is used as the unit object of the monoidal structure, which makes it hard to recover the original universe level.
