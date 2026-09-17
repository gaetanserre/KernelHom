/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import KernelHom.Tactic.KernelCat
import VersoManual

open Verso.Genre Manual Verso.Genre.Manual.InlineLean Verso.Code.External Mathlib.Tactic

set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "Categorical tactics for kernels" =>
%%%
htmlSplit := .never
%%%

Two of the most powerful tactics for categories in Mathlib are {name Monoidal.monoidal}`monoidal` and {name Coherence.coherence}`coherence`. To facilitate the use of these tactics for kernel equalities, *Kernel-Hom* provides the {name kernelDisch}`kernel_disch`, {name kernelMonoidal}`kernel_monoidal`, {name kernelCoherence}`kernel_coherence` and {name aesopKernel}`aesop_kernel` tactics which first apply {name kernelHom}`kernel_hom` to the goal to translate the kernel equality into a categorical equality in the {name SFinKer}`SFinKer` category, then apply, respectively, {name CategoryTheory.categoryTheoryDischarger}`cat_disch` and {name Monoidal.monoidal}`monoidal`, {name Monoidal.monoidal}`monoidal`, {name Coherence.coherence}`coherence`, or `aesop` (with the `CategoryTheory` rule set) to solve or simplify the categorical equality. {name kernelDisch}`kernel_disch` is the tactic to use by default: it tries both {name CategoryTheory.categoryTheoryDischarger}`cat_disch` and {name Monoidal.monoidal}`monoidal`, and before giving up, it also normalizes the tensor products of morphisms, which allows it to use the exchange law and the comonoid laws of copy and discard, including for deterministic and Markov kernels.

{docstring kernelDisch}

{docstring kernelMonoidal}

{docstring kernelCoherence}

{docstring aesopKernel}

For more details on the implementation of the {name Monoidal.monoidal}`monoidal` and {name Coherence.coherence}`coherence` tactics, see the [documentation](https://yuma-mizuno.github.io/coherence-tactics/) made by [@Yuma Mizuno](https://yuma-mizuno.github.io/).
