/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import KernelHomTests.Basu
import KernelHomManual.Papers
import KernelHomManual.Tools.VersoKernelDiagram
import KernelHomManual.Tools.LeanDecl
import VersoManual

open Verso.Genre Manual Verso.Genre.Manual.InlineLean Verso.Code.External Mathlib.Tactic

open ProbabilityTheory Kernel KernelHom

set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option pp.rawOnError true
set_option verso.code.warnLineLength 100
set_option verso.exampleProject "."
set_option verso.exampleModule "KernelHomTests.Basu"

#doc (Manual) "Calculational proofs" =>
%%%
htmlSplit := .never
tag := "calculational-proofs"
%%%

In Mathlib, proofs by calculation whose steps are equalities of kernels are rare. Calculations on measures built from kernels are more common, but each of their structural steps, such as reassociating a composition, marginalizing with {name ProbabilityTheory.Kernel.discard}`Kernel.discard`, or moving a kernel along {name ProbabilityTheory.Kernel.copy}`Kernel.copy`, is a chain of rewritings with lemmas about kernels and measures. With *Kernel-Hom*, these steps are closed by {name kernelDisch}`kernel_disch`, in the same way as {name CategoryTheory.cat_disch}`cat_disch` closes easy steps of categorical proofs.

A proof can therefore be written as a `calc` whose lines are the mathematically meaningful rewrites, typically by hypotheses. To apply a rewrite, the kernels are first arranged so that the hypothesis appears, and the remaining equality only differs by the structure of the kernels (composition, parallel composition, copy, discard, swap). {name kernelDisch}`kernel_disch` closes it. Each step of the calculation can moreover be visualized with string diagrams.

# Basu's theorem

As an example, we formalize Theorem 15.8 of {citep fritz2020}[], which is the main ingredient of the classical Basu theorem: a complete sufficient statistic is independent of any ancillary statistic, for every value of the parameter. A statistical model is a Markov kernel `p : Kernel Θ X`, and almost sure equality, sufficiency, completeness and ancillarity are all defined by equalities of kernels:

```VersoTools.leanDecl
ProbabilityTheory.Kernel.AEEq
ProbabilityTheory.Kernel.IsSufficient
ProbabilityTheory.Kernel.IsComplete
ProbabilityTheory.Kernel.IsAncillary
```

The proof consists of two calculations. The first one shows that `a ∘ₖ α` and `ψ ∘ₖ discard V` agree after `s ∘ₖ p`, where `α` witnesses the sufficiency of `s` and `ψ` the ancillarity of `a`:

```VersoTools.leanDecl
ProbabilityTheory.Kernel.basu_aux
```

The visible rewrites are the sufficiency equation `hα` and the ancillarity equation `hψ`. The first line marginalizes the right-hand side of the sufficiency equation, so that `hα` can be applied. After each rewrite, {name kernelDisch}`kernel_disch` proves the remaining equality.

The second calculation uses the completeness of `s ∘ₖ p` on the first one:

```VersoTools.leanDecl
ProbabilityTheory.Kernel.basu
```

The visible rewrites are the sufficiency equation `hα`, the completeness of `s ∘ₖ p` (`h`) and the ancillarity equation `hψ`. The last calculation step before the ancillarity is the factorization of Theorem 15.8 of {citep fritz2020}[], where the joint distribution of `s` and `a` is the product of `s ∘ₖ p` and of the distribution `ψ`.

# String diagrams of the calculation

Each step of the two calculations is stated as a lemma in `KernelHomTests/Basu.lean`, so that its string diagrams can be drawn. The diagrams are read from top to bottom.

## First calculation

Step 1. Marginalization of the right-hand side of the sufficiency equation.

```VersoTools.kernelDiagram
ProbabilityTheory.Kernel.basu_aux_step₁
```

Step 2. By sufficiency.

```VersoTools.kernelDiagram
ProbabilityTheory.Kernel.basu_aux_step₂
```

Step 3. By ancillarity.

```VersoTools.kernelDiagram
ProbabilityTheory.Kernel.basu_aux_step₃
```

## Second calculation

Step 1. Arrangement of the kernels so that the sufficiency equation appears.

```VersoTools.kernelDiagram
ProbabilityTheory.Kernel.basu_step₁
```

Step 2. By sufficiency.

```VersoTools.kernelDiagram
ProbabilityTheory.Kernel.basu_step₂
```

Step 3. By completeness, with the first calculation.

```VersoTools.kernelDiagram
ProbabilityTheory.Kernel.basu_step₃
```

Step 4. The factorization of Theorem 15.8.

```VersoTools.kernelDiagram
ProbabilityTheory.Kernel.basu_step₄
```

Step 5. By ancillarity.

```VersoTools.kernelDiagram
ProbabilityTheory.Kernel.basu_step₅
```
