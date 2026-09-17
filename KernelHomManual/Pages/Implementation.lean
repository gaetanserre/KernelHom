/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import KernelHom.Tactic.KernelHom
import EqLift.Tactic.Cache
import EqLift.Tactic.Kernel.Utils
import VersoManual

open Verso.Genre Manual Verso.Genre.Manual.InlineLean Verso.Code.External

set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "Implementation of the translation" =>
%%%
htmlSplit := .never
tag := "implementation"
%%%

The translation performed by {name kernelHom}`kernel_hom` traverses the kernel expression twice (once to lift it to a common universe level, once to translate it into {name SFinKer}`SFinKer`) and builds, at each node, an instance of a translation lemma such as {name ProbabilityTheory.Kernel.comp_hom}`comp_hom` or {name ProbabilityTheory.Kernel.comp_lift}`comp_lift`. Two design choices keep this cheap.

# Proofs by congruence

The proof of equivalence between the original equality and the translated one is not obtained by rewriting the goal with the translation lemmas (which requires abstracting a pattern and type-checking a motive at each step), but by congruence: each translation function returns the translated expression together with a proof that it is the translation of the original one, built from the proofs of its subterms with {name Lean.Meta.mkCongr}`mkCongr`, {name Lean.Meta.mkCongrArg}`mkCongrArg` and {name Lean.Meta.mkEqTrans}`mkEqTrans`. The equality of propositions is then obtained from {name ProbabilityTheory.Kernel.hom_congr}`hom_congr` (or {name ProbabilityTheory.Kernel.lift_congr}`lift_congr`) and `propext`, see {name mkHomCongrProof}`mkHomCongrProof`.

{docstring mkHomCongrProof}

# Explicit constructors and memoization

The terms and lemma instances are built directly with `mkAppN`, with explicit universe levels and instances, instead of `mkAppM`, whose unification and instance synthesis dominated the cost of the translation. This requires a fixed order of the universe parameters of the translation lemmas, which is why the universes of `KernelHom.Kernel.Hom` are declared explicitly (`x y t z u x₀ y₀ z₀`).

The instances (`MeasurableSpace X`, `IsSFiniteKernel κ`, the category-theoretic instances of {name SFinKer}`SFinKer`, ...), the inferred types of kernels and the recursively built objects (measurable equivalences, objects of {name SFinKer}`SFinKer`) are memoized in a cache which is reset at the beginning of each transformation. The cache lives in *Eq-Lift*:

{docstring TransformCache}

{docstring resetTransformCache}

{docstring synthInstanceCached}

{docstring inferTypeCached}

{docstring memoized}

# Carriers

A measurable space is represented during the transformations by its carrier type and universe level, from which the `MeasurableSpace` instance is obtained through the cache.

{docstring Carrier}

{docstring Carrier.inst}

{docstring Carrier.lift}

{docstring getCarriersFromKernel}

{docstring constructMeasurableEquiv}

The translation to {name SFinKer}`SFinKer` needs more data about each carrier `X`: the object of {name SFinKer}`SFinKer` it is translated to (`SFinKer.of X`, or a tensor product of such objects when `X` is a product, so that the monoidal tactics see the tensor structure) and the measurable equivalence between the carrier of this object and `X`, which is the argument `ex` of {name ProbabilityTheory.Kernel.hom}`hom` and of the translation lemmas. These are computed once per carrier by {name computeSFinkerOf}`computeSFinkerOf` and {name idME}`idME`, and gathered in a {name HomCarrier}`HomCarrier`.

{docstring HomCarrier}

{docstring HomCarrier.mk'}

{docstring HomCarrier.sfinite}

{docstring computeSFinkerOf}

{docstring idME}

Finally, every morphism built during the translation (`≫`, `⊗ₘ`, whiskers, `𝟙`, `ε`, `Δ`, braiding) takes as implicit arguments the category-theoretic instances of {name SFinKer}`SFinKer` (`Category`, `MonoidalCategory`, ...). Since the constructors are explicit, these instances have to be provided, and they are synthesized once per universe level and gathered in a {name SFinKerInsts}`SFinKerInsts`, which also provides the constructors of the morphisms.

{docstring SFinKerInsts}

{docstring sfinkerInsts}
