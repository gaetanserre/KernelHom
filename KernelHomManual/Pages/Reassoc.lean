/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import KernelHomTests.Examples
import KernelHomManual.Tools.VersoKernelDiagram
import KernelHomManual.Tools.LeanDecl
import KernelHom.Tactic.Reassoc
import VersoManual

open Verso.Genre Manual Verso.Genre.Manual.InlineLean Verso.Code.External Mathlib.Tactic
open ProbabilityTheory.Kernel

open ProbabilityTheory Kernel KernelHom

open scoped CategoryTheory.ComonObj

set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option pp.rawOnError true
set_option verso.code.warnLineLength 100
set_option verso.exampleProject "."
set_option verso.exampleModule "KernelHomTests.Examples"

#doc (Manual) "Kernel reassociation" =>
%%%
htmlSplit := .never
%%%

The translation of kernels to morphisms in the {name SFinKer}`SFinKer` category allows to adapt the
`@[reassoc]` attribute to equalities of s-finite kernels.

To this end, the library provides the `@[kernel_reassoc]` attribute, which is a variant of `@[reassoc]` that, given a lemma named `F` of shape `∀ .., f = g`, where `f g : Kernel X Y` are
s-finite kernels, will create a new lemma named `F_assoc` of shape `∀ .. {Z : Type u} [MeasurableSpace Z] (ξ : Kernel Y Z) [IsSFiniteKernel], ξ ∘ₖ f = ξ ∘ₖ g`.
As a new measurable space `Z` is introduced, the new declaration has a new universe level, which prevents the use of the `@[reassoc]` pipeline. Instead, `@[kernel_reassoc]` mirrors the structure of `@[reassoc]` but uses the {name kernelReassocHandler}`kernelReassocHandler` function to generate the proof of the new declaration. It first transforms the kernel equality into a categorical equality in `SFinKer`, then applies the `@[reassoc]` pipeline to generate the reassociated equality, and finally transforms the result back into a kernel equality.

{docstring kernelReassocHandler}

# Example

The `@[kernel_reassoc]` attribute works the exact same way as `@[reassoc]`, but for equalities of s-finite kernels:

```VersoTools.leanDecl
ProbabilityTheory.Kernel.parallelComp_self_comp_copy'
```

```lean -show
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
variable (κ : Kernel (X × Y) Z) [IsMarkovKernel κ] [IsDeterministic κ]
```

```lean (name := parallelComp_self_comp_copy_assoc)
variable {W : Type*} [MeasurableSpace W] (ξ : Kernel (Z × Z) W) [IsSFiniteKernel ξ]
#check parallelComp_self_comp_copy'_assoc κ ξ
```
```leanOutput parallelComp_self_comp_copy_assoc
parallelComp_self_comp_copy'_assoc κ ξ : ξ ∘ₖ (κ ∥ₖ κ) ∘ₖ copy (X × Y) = ξ ∘ₖ copy Z ∘ₖ κ
```
