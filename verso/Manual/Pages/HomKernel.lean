/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import VersoManual

open Verso.Genre Manual Verso.Genre.Manual.InlineLean Verso.Code.External

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100
set_option verso.exampleProject "../"
set_option verso.exampleModule "KernelHom.Tactic.Hom.HomKernel"

#doc (Manual) "HomKernel tactic" =>
%%%
htmlSplit := .never
%%%

The {anchorTerm hom_kernel_tactic}`hom_kernel` tactic is the inverse of {anchorTerm example_hom_kernel}`kernel_hom`. It transforms categorical equalities in the [`SFinKer`](doc/Mathlib/Probability/Kernel/Category/SFinKer.html#SFinKer) category back into equivalent kernel equalities. For example, given morphisms `κ.hom ≫ η.hom = ξ.hom` in the [`SFinKer`](doc/Mathlib/Probability/Kernel/Category/SFinKer.html#SFinKer) category, the tactic transforms it back to the kernel equality `η ∘ₖ κ = ξ`.

The tactic can be described in 3 steps:

1. First, it recursively traverses the categorical equality and creates a new expression where each morphism is replaced by its translation as a kernel expression, uniformly un-lifting carrier spaces from the common universe level to their original universe levels using measurable equivalences. During this process, it recognizes patterns of categorical composition and identities, and translates them to the corresponding kernel operations (composition, identity, parallel composition, etc...). This is done using the {anchorTerm transformHomToKernel}`transformHomToKernel` function.

1. Next, it constructs the proof of equivalence between the original kernel equality and the transformed categorical equality. This proof relies on the properties of the translation (e.g., that it preserves composition and identities) and on the fact that all kernels can be uniformly lifted to the common universe level using measurable equivalences.

1. Finally, it replaces the original goal or hypothesis with the transformed one.

Note that when `PUnit` is encountered during the un-lifting process, it un-lifts to `Unit`, no matter the universe level of the original `PUnit` carrier. This is because `PUnit` is used as the unit object of the monoidal structure, which makes it hard to recover the original universe level.
