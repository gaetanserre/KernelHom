/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import VersoManual

open Verso.Genre Manual Verso.Genre.Manual.InlineLean Verso.Code.External

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100
set_option verso.exampleProject "."
set_option verso.exampleModule "KernelHom.Tactic.KernelCat"

#doc (Manual) "Categorical tactics for kernels" =>
%%%
htmlSplit := .never
%%%

Two of the most powerful tactics for categories is Mathlib are {anchorTerm kernel_monoidal_tactic}`monoidal` and {anchorTerm kernel_coherence_tactic}`coherence`. To facilitate the use of these tactics for kernel equalities, we provide the {anchorTerm kernel_monoidal_tactic}`kernel_monoidal` and {anchorTerm kernel_coherence_tactic}`kernel_coherence` tactics, which first apply {anchorTerm kernel_coherence_tactic}`kernel_hom` to the goal to translate the kernel equality into a categorical equality in the [`SFinKer`](doc/Mathlib/Probability/Kernel/Category/SFinKer.html#SFinKer) category, then apply {anchorTerm kernel_monoidal_tactic}`monoidal` or {anchorTerm kernel_coherence_tactic}`coherence` to solve or simplify the categorical equality.
