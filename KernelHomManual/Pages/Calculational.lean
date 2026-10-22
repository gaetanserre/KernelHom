/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import KernelHomTests.KernelHom.Paper.DataAugmentation
import KernelHomManual.Papers
import KernelHomManual.Tools.LeanDecl
import VersoManual

open Verso.Genre Manual Verso.Genre.Manual.InlineLean Verso.Code.External Mathlib.Tactic

open ProbabilityTheory Kernel KernelHom

set_option verso.exampleProject "."
set_option verso.exampleModule "KernelHomTests.KernelHom.Paper.DataAugmentation"

#doc (Manual) "Calculational proofs" =>
%%%
htmlSplit := .never
tag := "calculational-proofs"
%%%

In Mathlib, proofs by calculation whose steps are equalities of kernels are rare. Each of their structural steps is a chain of rewritings, which buries the meaningful steps. Such steps are, e.g., reassociating a composition, marginalizing an output or moving a kernel along a copy. With *Kernel-Hom*, the structural steps are proved by {name kernelDisch}`kernel_disch`, in the same way as {name CategoryTheory.categoryTheoryDischarger}`cat_disch` or {name Monoidal.monoidal}`monoidal` proves the easy steps of categorical proofs. Thus, a proof can be written as a `calc` whose lines are the meaningful rewrites. With {name MeasureKernel.measureKernel}`measure_kernel`, this also holds for calculations on measures built from kernels. On paper, the structural steps are invisible. Indeed, they relate string diagrams that only differ by a deformation of the wires or by the axioms of copy-discard categories.

# Reversibility of data augmentation
%%%
tag := "data-augmentation"
%%%

We illustrate this with {citet douc2018}[], about data augmentation algorithms.

*Statement*

Let $`\mathsf{X}` and $`\mathsf{Y}` be Polish spaces, equipped with their Borel σ-fields $`\mathcal{X}` and $`\mathcal{Y}`. Let $`\pi` be a probability measure on $`\mathsf{X}` and $`R` a Markov kernel from $`\mathsf{X}` to $`\mathsf{Y}`. By disintegration, there exist a kernel $`S` from $`\mathsf{Y}` to $`\mathsf{X}` and a probability measure $`\tilde\pi` on $`\mathsf{Y}` such that

$$`\pi(\mathrm{d}x)\, R(x, \mathrm{d}y) = S(y, \mathrm{d}x)\, \tilde\pi(\mathrm{d}y). \qquad (2.3.11)`

A data augmentation algorithm draws $`y` from $`R(x, \cdot)`, then $`x` from $`S(y, \cdot)`. Thus, the sequence of the $`x` is a Markov chain with kernel $`RS(x, A) = \int R(x, \mathrm{d}y)\, S(y, A)`.

_Lemma 2.3.5._ The distribution $`\pi` is reversible with respect to the kernel $`RS`, i.e. the measure $`\pi \otimes RS` on $`\mathsf{X} \times \mathsf{X}` is symmetric (Definition 1.5.1):

$$`\forall A, B \in \mathcal{X}, \quad \pi \otimes RS(A \times B) = \pi \otimes RS(B \times A).`

_Proof._ Let $`A, B \in \mathcal{X}`. Using (2.3.11), we have that

$$`\begin{aligned} \pi \otimes RS(A \times B) &= \int \pi(\mathrm{d}x)\, R(x, \mathrm{d}y)\, \mathbb{1}_A(x)\, S(y, B) \\ &= \int S(y, \mathrm{d}x)\, \tilde\pi(\mathrm{d}y)\, \mathbb{1}_A(x)\, S(y, B) \\ &= \int S(y, A)\, S(y, B)\, \tilde\pi(\mathrm{d}y), \end{aligned}`

which is symmetric in $`A` and $`B`.

*Formalization*

In Mathlib, $`S` is the posterior `R†π` ({name ProbabilityTheory.posterior}`posterior`) and $`\tilde\pi` is `R ∘ₘ π`. The kernel $`RS` is `S ∘ₖ R`, and the measure $`\pi \otimes RS` is `π ⊗ₘ (S ∘ₖ R)`. The reversibility {name ProbabilityTheory.Kernel.IsReversible}`IsReversible` is defined by the equality of the integrals of $`RS(\cdot, B)` over $`A` and of $`RS(\cdot, A)` over $`B`. The lemma {name ProbabilityTheory.Kernel.DataAugmentation.isReversible_of_map_swap}`isReversible_of_map_swap` derives it from the symmetry of the measure, stated as its invariance by the swap of the coordinates.

```VersoTools.leanDecl
ProbabilityTheory.Kernel.DataAugmentation.isReversible_of_map_swap
ProbabilityTheory.Kernel.DataAugmentation.isReversible_comp
```

The formal proof has the structure of the proof of the book. The hypothesis `h` is equation (2.3.11), which follows from {name ProbabilityTheory.compProd_posterior_eq_swap_comp}`compProd_posterior_eq_swap_comp`. The calculation `key` is the computation of the book, and its only meaningful step is the rewrite with `h`. The symmetry of the right-hand side of `key` is the cocommutativity of the copy. All the other steps are structural, and are proved by {name MeasureKernel.measureKernel}`measure_kernel` followed by {name kernelDisch}`kernel_disch`. Without the tactics, the last step of `key` can be proved with the lemmas of Mathlib by

```
rw [Measure.compProd_eq_comp_prod, Measure.comp_assoc, Measure.comp_assoc, Kernel.comp_assoc,
  swap_prod, parallelComp_comp_prod, Kernel.id_comp, Kernel.comp_id]
```

which requires knowing seven lemmas about kernels and measures, and reassociating the compositions by hand so that each rewrite applies.
