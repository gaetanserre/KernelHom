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
set_option verso.exampleModule "KernelHom.Tactic.Hom.KernelHom"

#doc (Manual) "KernelHom tactic" =>
%%%
htmlSplit := .never
%%%

The {anchorTerm kernel_hom_tactic}`kernel_hom` tactic transforms a kernel equality into an equality in the [`SFinKer`](doc/Mathlib/Probability/Kernel/Category/SFinKer.html#SFinKer) category, where categorical tactics can be applied to simplify it. For example, given kernels `κ : Kernel X Y`, `η : Kernel Y Z` and `ξ : Kernel X Z`, the following kernel equality: `η ∘ₖ κ = ξ` is transformed to `κ.hom ≫ η.hom = ξ.hom` in the [`SFinKer`](doc/Mathlib/Probability/Kernel/Category/SFinKer.html#SFinKer) category, where [`hom`](doc/KernelHom/Hom.html#ProbabilityTheory.Kernel.hom) is the translation of kernels to morphisms in [`SFinKer`](doc/Mathlib/Probability/Kernel/Category/SFinKer.html#SFinKer).

The tactic can be described in 4 steps:

1. First, it finds the minimum common universe level for which all carrier spaces of the kernels involved in the equality can be lifted to.

1. Then, it recursively traverses the kernel equality and creates a new expression where each kernel is replaced by its translation in the [`SFinKer`](doc/Mathlib/Probability/Kernel/Category/SFinKer.html#SFinKer) category, uniformly lifting carrier spaces to the common universe level determined in the first step. During this process, it recognizes patterns of kernel composition and identities, and translates them to the corresponding categorical operations (composition, identity, unitors, whiskers, monoidal composition, etc...). This is done using the {anchorTerm transformKernelToHom}`transformKernelToHom` function.

1. Next, it constructs the proof of equivalence between the original kernel equality and the transformed categorical equality. This proof relies on the properties of the translation (e.g., that it preserves composition and identities) and on the fact that all kernels can be uniformly lifted to the common universe level using measurable equivalences.

1. Finally, it replaces the original goal or hypothesis with the transformed one.

# Usage examples

The tactic {anchorTerm kernel_hom_tactic}`kernel_hom` allows users to leverage categorical reasoning or powerful categorical tactics to simplify kernel equalities.

```anchor example_kernel_hom1
example : ξ ∘ₖ (η ∘ₖ κ) = ξ ∘ₖ η ∘ₖ κ := by
  kernel_hom
  simp only [Category.assoc]
```

```anchor example_kernel_hom2
example : (η ∘ₖ Kernel.id.map (Prod.fst : Y × PUnit → Y)) ∘ₖ
    (Kernel.id.map (Prod.fst : Y × PUnit → Y) ∥ₖ Kernel.id (α := PUnit)) ∘ₖ
      ((κ ∥ₖ Kernel.id (α := PUnit)) ∥ₖ Kernel.id (α := PUnit))
    = (η ∘ₖ κ ∘ₖ (Kernel.id.map (Prod.fst : X × PUnit → X)) ∘ₖ
      ((Kernel.id.map (Prod.fst : X × PUnit → X)) ∥ₖ Kernel.id (α := PUnit))
    : Kernel ((X × PUnit) × PUnit) Z)
     := by
  kernel_hom; monoidal
```
