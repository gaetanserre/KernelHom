/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import VersoManual
import KernelHomManual.Papers
import KernelHomManual.Pages.Examples
import KernelHomManual.Pages.Universe
import KernelHomManual.Pages.KernelHom
import KernelHomManual.Pages.HomKernel
import KernelHomManual.Pages.CatTactics
import KernelHomManual.Pages.MonoidalComp
import KernelHom.Tactic.Hom.KernelDiagram
import Mathlib.Probability.Kernel.Category.Stoch

open Verso.Genre Manual Verso.Genre.Manual.InlineLean Mathlib.Tactic

set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option pp.rawOnError true

#doc (Manual) "Kernel-Hom: Tactics for Kernel Categorical Reasoning" =>
%%%
authors := ["Gaëtan Serré"]
shortTitle := "Kernel Categorical Reasoning"
%%%

*Overview*

*Kernel-Hom* is a Lean 4 library that provides tactics to simplify kernel equalities by leveraging categorical reasoning. It automatically translates s-finite kernel equalities into equalities in a monoidal category, where tactics like {name Monoidal.monoidal}`monoidal` or {name Coherence.coherence}`coherence` can be applied, and then translates the result back to a kernel equality if needed. The translation from kernels to categorical expressions also allows to use any tool from category theory within the context of kernels, such as string diagram visualization or monoidal composition.

![](static/diagram.svg)

*Documentation*

The complete documentation for the library is available in the [API reference](doc/).

*Core of the project*

The library introduces two main tactics:
- {name kernelHom}`kernel_hom` : transforms a kernel equality into an equality in the monoidal category.
- {name homKernel}`kernel_hom` : performs the inverse transformation, bringing the categorical equality back to a kernel equality.

These tactics allow users to transform complex kernel equalities into categorical equalities, where powerful categorical tactics can be applied to simplify or prove them. To this end, the library provides built-in helpers like {name kernelMonoidal}`kernel_monoidal` and {name kernelCoherence}`kernel_coherence` to apply categorical tactics directly to kernels without needing to manually invoke the translation tactics.

The library rests on {name SFinKer}`SFinKer`, the category of measurable spaces with s-finite kernels as morphisms, equipped with monoidal and symmetric structures. This category is also used to define {name Stoch}`Stoch`, the category of measurable spaces with Markov kernels as morphisms, which is a wide subcategory of {name SFinKer}`SFinKer` (see {citep fritz2020}[]). Both categories have been merged into Mathlib (PR [#36779](https://github.com/leanprover-community/mathlib4/pull/36779)).

*Universe handling*

A key aspect of the library is automatic universe management: expressions are lifted to a common universe level during translation, ensuring categorical expressions are well-typed. This allows users to work with kernels of varying universe levels without needing to manually manage universe annotations.

*Kernel diagrams*

The library provides the {name kernelDiagram}`kernel_diagram` command, which generates string diagrams for kernel expressions. This is an adaptation of the {name Widget.stringDiagram}`string_diagram` command, where s-finite kernels are represented as morphisms using {name kernelHom}`kernel_hom`. This provides a visual representation of kernel compositions and transformations, aiding intuition and understanding. The visualization of such diagrams in this documentation is made possible by the Verso code block expander made by [@Yuma Mizuno](https://github.com/yuma-mizuno/coherence-tactics/blob/master/CoherenceTactics/VersoStringDiagram.lean).

*Kernelized monoidal composition*

An additional consequence of the translation to {name SFinKer}`SFinKer` is that one can adapt the categorical monoidal composition “{name CategoryTheory.monoidalComp}`⊗≫`” to kernels, resulting in a kernelized monoidal composition “{name ProbabilityTheory.Kernel.monoComp}`⊗≫ₖ`”. This composition automatically handles measurable equivalences, allowing for seamless composition of kernels while maintaining s-finiteness.

*About*

This library is under active development and is under the [GNU GPL 3.0 license](https://www.gnu.org/licenses/gpl-3.0.en.html). Contributions and feedback are welcome!

{include 0 KernelHomManual.Pages.Examples}

{include 0 KernelHomManual.Pages.Universe}

{include 0 KernelHomManual.Pages.KernelHom}

{include 0 KernelHomManual.Pages.HomKernel}

{include 0 KernelHomManual.Pages.CatTactics}

{include 0 KernelHomManual.Pages.MonoidalComp}
