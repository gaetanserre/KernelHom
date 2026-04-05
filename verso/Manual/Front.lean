/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import VersoManual
import Manual.Papers
import Manual.Pages.Universe
import Manual.Pages.KernelHom
import Manual.Pages.HomKernel
import Manual.Pages.CatTactics

open Verso.Genre Manual Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "KernelHom: Tactics for Categorical Kernel Reasoning" =>
%%%
authors := ["Gaëtan Serré"]
shortTitle := "Categorical Kernel Reasoning"
%%%

*Overview*

*Kernel Hom* is a Lean 4 library that provides tactics to simplify kernel equalities by leveraging categorical reasoning. It automatically translates kernel equalities into equalities in a monoidal category, where tactics like [`coherence`](doc/Mathlib/Tactic/CategoryTheory/Coherence.html#Mathlib.Tactic.Coherence.coherence) or [`monoidal`](doc/Mathlib/Tactic/CategoryTheory/Monoidal/Basic.html#Mathlib.Tactic.Monoidal.monoidal) can be applied, and then translates the result back to a kernel equality.

![](static/diagram.svg)

*Documentation*

The complete documentation for the library is available in the [API reference](doc/).

*Core of the project*

The library introduces two main tactics:
- [`kernel_hom`](doc/KernelHom/Tactic/Hom/KernelHom.html#tacticKernel_hom__) : transforms a kernel equality into an equality in the monoidal category.
- [`hom_kernel`](doc/KernelHom/Tactic/Hom/HomKernel.html#tacticHom_kernel__) : performs the inverse transformation, bringing the categorical equality back to a kernel equality.

These tactics allow users to transform complex kernel equalities into categorical equalities, where powerful categorical tactics can be applied to simplify or prove them. To this end, the library provides built-in helpers like `kernel_coherence` and `kernel_monoidal` to apply categorical tactics directly to kernels without needing to manually invoke the translation tactics.

The library rests on [`SFinKer`](doc/Mathlib/Probability/Kernel/Category/SFinKer.html#SFinKer), the category of measurable spaces with s-finite kernels as morphisms, equipped with monoidal and symmetric structures. This category is also used to define [`Stoch`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Category/Stoch.html#Stoch), the category of measurable spaces with Markov kernels as morphisms, which is a wide subcategory of [`SFinKer`](doc/Mathlib/Probability/Kernel/Category/SFinKer.html#SFinKer) (see {citep fritz2020}[]). Both categories have been merged into Mathlib (PR [#36779](https://github.com/leanprover-community/mathlib4/pull/36779)).

*Universe handling*

A key aspect of the library is automatic universe management: expressions are lifted to a common universe level during translation, ensuring categorical expressions are well-typed. This allows users to work with kernels of varying universe levels without needing to manually manage universe annotations.

*About*

This library is under active development and is under the [GNU GPL 3.0 license](https://www.gnu.org/licenses/gpl-3.0.en.html). Contributions and feedback are welcome!

{include 0 Manual.Pages.Universe}

{include 0 Manual.Pages.KernelHom}

{include 0 Manual.Pages.HomKernel}

{include 0 Manual.Pages.CatTactics}
