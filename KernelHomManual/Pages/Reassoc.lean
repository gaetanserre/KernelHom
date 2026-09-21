/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import KernelHom
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

#doc (Manual) "Kernel reassociation" =>
%%%
htmlSplit := .never
%%%

The composition of kernels associates to the left: `ξ ∘ₖ η ∘ₖ κ` stands for `(ξ ∘ₖ η) ∘ₖ κ`. An equality `h : η ∘ₖ κ = ζ` therefore cannot rewrite this kernel, since `η ∘ₖ κ` is not one of its subterms: `rw [h]` fails, and one first has to reassociate with {name ProbabilityTheory.Kernel.comp_assoc}`Kernel.comp_assoc`. The composition `≫` of morphisms in a category raises the same issue, which Mathlib solves with the attribute `@[reassoc]`. From a lemma `F : f = g` with `f g : X ⟶ Y`, it generates the lemma `F_assoc : ∀ {Z} (h : Y ⟶ Z), f ≫ h = g ≫ h`, whose two sides are normalized with the associativity of `≫`, so that `F_assoc` rewrites `f` inside longer compositions. The translation of kernels to morphisms of {name SFinKer}`SFinKer` allows to adapt this attribute to kernels.

# The `@[kernel_reassoc]` attribute

From a lemma `F` whose conclusion is `f = g` with `f g : Kernel X Y` s-finite kernels, `@[kernel_reassoc]` generates a lemma `F_assoc` with the same hypotheses and the conclusion
`∀ {Z : Type u} [MeasurableSpace Z] (ξ : Kernel Y Z) [IsSFiniteKernel ξ], ξ ∘ₖ f = ξ ∘ₖ g`,
where both sides are normalized so that all the compositions associate to the left. For instance:

```lean -show
variable {X Y Z Y' Z' : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  [MeasurableSpace Y'] [MeasurableSpace Z']
variable (κ : Kernel X Y) [IsSFiniteKernel κ] (η : Kernel Y Z)
    [IsSFiniteKernel η] (κ' : Kernel X Y') [IsSFiniteKernel κ'] (η' : Kernel Y' Z')
    [IsSFiniteKernel η']
```

```lean
@[kernel_reassoc]
lemma parallelComp_comp_prod₀ : (η ∥ₖ η') ∘ₖ (κ ×ₖ κ') = (η ∘ₖ κ) ×ₖ (η' ∘ₖ κ') := by
  kernel_disch
```

```lean -show
variable {W: Type*} [MeasurableSpace W] (ξ : Kernel (Z × Z') W) [IsSFiniteKernel ξ]
```

```lean (name := parallelComp_comp_prod_assoc)
#check parallelComp_comp_prod₀_assoc κ η κ' η' ξ
```
```leanOutput parallelComp_comp_prod_assoc
parallelComp_comp_prod₀_assoc κ η κ' η'
  ξ : ξ ∘ₖ (η ∥ₖ η') ∘ₖ (κ ∥ₖ κ') ∘ₖ copy X = ξ ∘ₖ (η ∘ₖ κ ∥ₖ (η' ∘ₖ κ')) ∘ₖ copy X
```

The attribute works by transport. The kernel equality is translated into an equality of morphisms of {name SFinKer}`SFinKer`, as in {name kernelHom}`kernel_hom`. The `@[reassoc]` pipeline of Mathlib is applied to this equality, and the result is translated back into kernels, as in {name homKernel}`hom_kernel`. The only subtlety concerns universes. The translation lifts all the carriers of `F` to a common level `w`, so the lemma produced by `@[reassoc]` quantifies over the objects `Z` of `SFinKer.{w}` only. Translated back, it would not apply to a kernel `ξ` whose codomain lives in an arbitrary universe. The equality is therefore lifted to `max u w`, where `u` is a fresh level for `Z`, and `u` becomes a new universe parameter of `F_assoc`.

{docstring kernelReassocHandler}

# The `kernel_reassoc_of%` elaborator

As `@[reassoc]` comes with the term elaborator `reassoc_of%`, `@[kernel_reassoc]` comes with `kernel_reassoc_of%`. For a proof `h` of an equality of s-finite kernels, `kernel_reassoc_of% h` is a proof of the reassociated equality, built as above. Unlike the attribute, it also applies to local hypotheses. For instance, it solves the rewriting problem described at the beginning of this page:

```lean
example {κ : Kernel X Y} {η : Kernel Y Z} {ζ : Kernel X Z} {ξ : Kernel Z W}
    [IsSFiniteKernel κ] [IsSFiniteKernel η] [IsSFiniteKernel ζ] [IsSFiniteKernel ξ]
    (h : η ∘ₖ κ = ζ) :
    ξ ∘ₖ η ∘ₖ κ = ξ ∘ₖ ζ := by
  rw [kernel_reassoc_of% h]
```
