/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import KernelHomTests.Examples
import KernelHomManual.Tools.VersoKernelDiagram
import KernelHomManual.Tools.LeanDecl
import VersoManual

open Verso.Genre Manual Verso.Genre.Manual.InlineLean Verso.Code.External Mathlib.Tactic

open ProbabilityTheory Kernel KernelHom

open scoped CategoryTheory.ComonObj

set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option pp.rawOnError true
set_option verso.code.warnLineLength 100
set_option verso.exampleProject "."
set_option verso.exampleModule "KernelHomTests.Examples"

#doc (Manual) "Usage and examples" =>
%%%
htmlSplit := .never
tag := "examples"
%%%

# Usage

To use *Kernel-Hom*, add the following to your `lakefile.toml`:
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

*Tactics*

The library provides several tactics for working with s-finite kernels equalities. The main tactics are:
- {name kernelHom}`kernel_hom`: Transforms a s-finite kernel equality into an equality in the {name SFinKer}`SFinKer` monoidal category.

- {name homKernel}`hom_kernel`: The inverse of {name kernelHom}`kernel_hom`, transforms an equality in {name SFinKer}`SFinKer` back into a kernel equality.

- {name kernelDisch}`kernel_disch`: The tactic to use by default. Applies the {name CategoryTheory.categoryTheoryDischarger}`cat_disch` and {name Monoidal.monoidal}`monoidal` tactics to a s-finite kernel equality, possibly after normalizing the tensor products of morphisms, so that it also handles the exchange law and the comonoid laws of copy and discard.

- {name kernelMonoidal}`kernel_monoidal`: Applies the {name Monoidal.monoidal}`monoidal` tactic to a s-finite kernel equality.

- {name kernelCoherence}`kernel_coherence`: Applies the {name Coherence.coherence}`coherence` tactic to a s-finite kernel equality.

- {name aesopKernel}`aesop_kernel`: Applies `aesop` with the `CategoryTheory` rule set to a s-finite kernel equality, without the `rfl_cat` attempt of {name CategoryTheory.categoryTheoryDischarger}`cat_disch`.

Basically, whenever you have a equality of s-finite kernels that you want to simplify, you can apply {name kernelHom}`kernel_hom` to transform it into a categorical equality, try applying categorical tactics, simps, or manually manipulate it, and then apply {name homKernel}`hom_kernel` to get back to a kernel equality if needed. The built-in helpers {name kernelDisch}`kernel_disch`, {name kernelMonoidal}`kernel_monoidal`, {name kernelCoherence}`kernel_coherence` and {name aesopKernel}`aesop_kernel` directly apply categorical tactics to kernels without needing to manually invoke the translation tactic.

*Kernel diagrams*

The library also provides the {name kernelDiagram}`kernel_diagram` command, which generates string diagrams for kernel expressions. This is an adaptation of the {name Widget.stringDiagram}`string_diagram` command, where s-finite kernels are represented as morphisms using {name kernelHom}`kernel_hom`. This provides a visual representation of kernel compositions and transformations, aiding intuition and understanding. The use of this command is similar to {name Widget.stringDiagram}`string_diagram`:

```lean
#kernel_diagram swap_prod₀
```

```VersoTools.kernelDiagram
swap_prod₀
```

# Examples

*Kernel-Hom* makes it easy to prove "API" lemmas about the usual operations on kernels. The following lemmas of Mathlib are equalities of kernels built only from composition, parallel composition, product, identity, copy and swap. In Mathlib, their proofs either manipulate integrals or rely on other lemmas about kernels. With *Kernel-Hom*, they are proved from the structure of {name SFinKer}`SFinKer`, without any knowledge of the lemmas about kernels. They are collected in the file `KernelHomTests/Examples.lean`, where their names are suffixed by `₀`. The tactics are also useful in longer proofs, written by calculation (see the {ref "calculational-proofs"}[calculational proof of Basu's theorem]).

The other lemmas of Mathlib built from these operations, such as {name ProbabilityTheory.Kernel.comp_assoc}`comp_assoc`, {name ProbabilityTheory.Kernel.swap_parallelComp}`swap_parallelComp` or {name ProbabilityTheory.Kernel.parallelComp_comp_parallelComp}`parallelComp_comp_parallelComp`, are used, directly or not, to prove the axioms of {name SFinKer}`SFinKer`. The tactics also prove them, but these proofs could not replace the ones of Mathlib, so they are not listed here.

As {name ProbabilityTheory.Kernel.map}`Kernel.map` is not translated, {name ProbabilityTheory.Kernel.map_prod_swap}`map_prod_swap` and {name ProbabilityTheory.Kernel.prodAssoc_prod}`prodAssoc_prod` are first rewritten with {name ProbabilityTheory.Kernel.swap_comp_eq_map}`swap_comp_eq_map` and {name ProbabilityTheory.Kernel.deterministic_comp_eq_map}`deterministic_comp_eq_map`. The tactics only apply to s-finite kernels: as in Mathlib, the case of a non s-finite kernel in {name ProbabilityTheory.Kernel.parallelComp_comm}`parallelComp_comm` is closed by `simp`.

All of them are proved by a single call to {name kernelDisch}`kernel_disch` or {name kernelMonoidal}`kernel_monoidal`. In particular, {name kernelDisch}`kernel_disch` handles the exchange law {name CategoryTheory.MonoidalCategory.whisker_exchange}`whisker_exchange` in {name ProbabilityTheory.Kernel.parallelComp_comm}`parallelComp_comm`, and the coassociativity of copy {name CategoryTheory.ComonObj.comul_assoc}`comul_assoc` in {name ProbabilityTheory.Kernel.prodAssoc_prod}`prodAssoc_prod`, which the tactics of Mathlib do not apply on their own.

*`Mathlib.Probability.Kernel.Composition.Prod`*

The kernel {name ProbabilityTheory.Kernel.swap}`Kernel.swap` is translated to the braiding of {name SFinKer}`SFinKer`, and the product `κ ×ₖ η` to the composition of the copy with `κ ⊗ₘ η`.

```VersoTools.leanDecl
ProbabilityTheory.Kernel.map_prod_swap₀
ProbabilityTheory.Kernel.swap_prod₀
```

```VersoTools.kernelDiagram
ProbabilityTheory.Kernel.swap_prod₀
```

```VersoTools.leanDecl
ProbabilityTheory.Kernel.prodAssoc_prod₀
```

*`Mathlib.Probability.Kernel.Composition.KernelLemmas`*

```VersoTools.leanDecl
ProbabilityTheory.Kernel.parallelComp_comp_prod₀
```

```VersoTools.kernelDiagram
ProbabilityTheory.Kernel.parallelComp_comp_prod₀
```

```VersoTools.leanDecl
ProbabilityTheory.Kernel.parallelComp_comm₀
```

The diagram below is drawn for s-finite kernels.

```VersoTools.kernelDiagram
fun {X Y Z T : Type} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace T]
    (κ : Kernel X Y) (η : Kernel Z T) [IsSFiniteKernel κ] [IsSFiniteKernel η] ↦
  parallelComp_comm₀ (κ := κ) (η := η)
```
