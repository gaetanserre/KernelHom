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
set_option verso.exampleModule "KernelHom.Tests.Examples"

#doc (Manual) "Usage and examples" =>
%%%
htmlSplit := .never
%%%

# Usage

To use `Kernel-Hom`, add the following to your `lakefile.toml`:
```
[[require]]
name = "kernelhom"
git = "https://github.com/gaetanserre/KernelHom.git"
```

or to your `lakefile.lean`:
```
require kernelhom from git "https://github.com/gaetanserre/KernelHom" @ "main"
```

Then, in your Lean files, you can import the library with:

```
import KernelHom
```

`Kernel-Hom` provides several tactics for working with s-finite kernels equalities. The main tactics are:
- {anchorTerm swap_parallelComp}`kernel_hom`: Transforms a s-finite kernel equality into an equality in the [`SFinKer`](doc/Mathlib/Probability/Kernel/Category/SFinKer.html#SFinKer) monoidal category.

- {anchorTerm dummy_example}`hom_kernel`: The inverse of {anchorTerm swap_parallelComp}`kernel_hom`, transforms an equality in [`SFinKer`](doc/Mathlib/Probability/Kernel/Category/SFinKer.html#SFinKer) back into a kernel equality.

- {anchorTerm parallelComp_id_left_comp_parallelComp}`kernel_monoidal`: Applies the [`monoidal`](doc/Mathlib/Tactic/CategoryTheory/Monoidal/Basic.html#Mathlib.Tactic.Monoidal.monoidal) tactic to a s-finite kernel equality.

- [`kernel_coherence`](doc/KernelHom/Tactic/KernelCat.html#tacticKernel_coherence): Applies the [`coherence`](doc/Mathlib/Tactic/CategoryTheory/Coherence.html#Mathlib.Tactic.Coherence.coherence) tactic to a s-finite kernel equality.

Basically, whenever you have a equality of s-finite kernels that you want to simplify, you can apply {anchorTerm swap_parallelComp}`kernel_hom` to transform it into a categorical equality, try applying categorical tactics, simps, or manually manipulate it, and then apply {anchorTerm dummy_example}`hom_kernel` to get back to a kernel equality if needed. The built-in helpers {anchorTerm parallelComp_id_left_comp_parallelComp}`kernel_monoidal` and [`kernel_coherence`](doc/KernelHom/Tactic/KernelCat.html#tacticKernel_coherence) directly apply categorical tactics to kernels without needing to manually invoke the translation tactic.

# Examples

These tactics are particularly useful when dealing with compositions and parallel compositions of kernels. The following examples are taken from the file [`KernelLemmas.lean`](doc/Mathlib/Probability/Kernel/Composition/KernelLemmas.html) and illustrate how the tactics can be used to drastically simplify the proofs of kernel equalities.

- [`parallelComp_id_left_comp_parallelComp`](doc/Mathlib/Probability/Kernel/Composition/KernelLemmas.html#ProbabilityTheory.Kernel.parallelComp_id_left_comp_parallelComp)

```anchor parallelComp_id_left_comp_parallelComp
example : (Kernel.id ∥ₖ ξ) ∘ₖ (κ ∥ₖ η) = κ ∥ₖ (ξ ∘ₖ η) := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  kernel_monoidal
```

- [`parallelComp_id_right_comp_parallelComp`](doc/Mathlib/Probability/Kernel/Composition/KernelLemmas.html#ProbabilityTheory.Kernel.parallelComp_id_right_comp_parallelComp)

```anchor parallelComp_id_right_comp_parallelComp
example : (ξ ∥ₖ Kernel.id) ∘ₖ (η ∥ₖ κ) = (ξ ∘ₖ η) ∥ₖ κ := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  kernel_monoidal
```

- [`parallelComp_comp_parallelComp`](doc/Mathlib/Probability/Kernel/Composition/KernelLemmas.html#ProbabilityTheory.Kernel.parallelComp_comp_parallelComp)

```anchor parallelComp_comp_parallelComp
example : (η ∥ₖ η') ∘ₖ (κ ∥ₖ κ') = (η ∘ₖ κ) ∥ₖ (η' ∘ₖ κ') := by
  kernel_monoidal
```

- [`parallelComp_comp_prod`](doc/Mathlib/Probability/Kernel/Composition/KernelLemmas.html#ProbabilityTheory.Kernel.parallelComp_comp_prod)

```anchor parallelComp_comp_prod
example : (η ∥ₖ η') ∘ₖ (κ ×ₖ κ') = (η ∘ₖ κ) ×ₖ (η' ∘ₖ κ') := by
  kernel_monoidal
```

- [`swap_parallelComp`](doc/Mathlib/Probability/Kernel/Composition/KernelLemmas.html#ProbabilityTheory.Kernel.swap_parallelComp)

  Object of the symmetric category are also handled by the tactic, such as [`Kernel.swap`](doc/Mathlib/Probability/Kernel/Basic.html#ProbabilityTheory.Kernel.swap) that is translated to the right braiding of [`SFinKer`](doc/Mathlib/Probability/Kernel/Category/SFinKer.html#SFinKer).

```anchor swap_parallelComp
example : swap Y T ∘ₖ (κ ∥ₖ ξ) = ξ ∥ₖ κ ∘ₖ swap X Z := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  by_cases hη : IsSFiniteKernel ξ
  swap; · simp [hη]
  kernel_hom
  exact braiding_naturality _ _
```

- [`deterministic_comp_copy`](doc/Mathlib/Probability/Kernel/Composition/KernelLemmas.html#ProbabilityTheory.Kernel.deterministic_comp_copy)

  The categorical counterpart of deterministic kernels are automatically treated as [`Deterministic`](doc/Mathlib/CategoryTheory/CopyDiscardCategory/Deterministic.html#CategoryTheory.Deterministic) morphisms.

```anchor deterministic_comp_copy
example {f : X → Y} (hf : Measurable f) :
    (deterministic f hf ∥ₖ deterministic f hf) ∘ₖ copy X = copy Y ∘ₖ deterministic f hf := by
  kernel_hom
  exact (Deterministic.copy_natural _).symm
```

```anchor discard_comp_deterministic
example {f : X → Y} (hf : Measurable f) :
    Kernel.discard Y ∘ₖ (deterministic f hf) = Kernel.discard X := by
  kernel_hom
  exact Deterministic.discard_natural _
```
