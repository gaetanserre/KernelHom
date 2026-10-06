/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import KernelHom.Tactic.HomKernel
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

The translation performed by {name kernelHom}`kernel_hom` traverses the kernel expression twice (once to lift it to a common universe level, once to translate it into {name SFinKer}`SFinKer`) and builds, at each node, an instance of a translation lemma such as {name ProbabilityTheory.Kernel.comp_toHom_of_eq}`comp_toHom_of_eq` or {name ProbabilityTheory.Kernel.comp_lift}`comp_lift`. Three design choices keep this cheap and safe.

# Proofs by congruence lemmas

The proof of equivalence between the original equality and the translated one is not obtained by rewriting the goal with the translation lemmas (which requires abstracting a pattern and type-checking a motive at each step), but by congruence: each translation function returns the translated expression together with a proof that it is the translation of the original one, built from the proofs of its subterms. The translation lemmas are stated for this purpose with the translations of the subterms as hypotheses, so that each step of the translation is a single application of a lemma:

{docstring ProbabilityTheory.Kernel.comp_toHom_of_eq}

The same lemmas serve both directions: {name kernelToHom}`kernelToHom` and {name homToKernel}`homToKernel` both return a proof of `f = κ.toHom`, where `f` is the morphism and `κ` the kernel. The equality of propositions is then obtained from {name ProbabilityTheory.Kernel.toHom_congr_of_eq}`toHom_congr_of_eq` (or {name ProbabilityTheory.Kernel.lift_congr}`lift_congr` for the lifting).

{docstring ProbabilityTheory.Kernel.toHom_congr_of_eq}

# Terms built with Qq

The terms and the lemma instances are built with the quotations `q(...)` of [Qq](https://github.com/leanprover-community/quote4). A quotation is elaborated when the tactic is compiled, and only instantiated at run time: the result is as cheap as an explicit application (`mkAppN` with explicit universe levels and instances), without the unification and instance synthesis of `mkAppM`, which dominated the cost of the translation. Moreover, the quotations are type-checked against the statements of the lemmas, so that an argument in the wrong position is a compilation error rather than an ill-typed proof at run time. The category-theoretic instances of {name SFinKer}`SFinKer` (`Category`, `MonoidalCategory`, ...) are synthesized at compilation as well.

The expressions are typed by the expressions of their types: `Q(Kernel $X $Y)` is the type of the expressions of a kernel from `X` to `Y`. The kernel and categorical expressions are matched syntactically, with `match_expr`, and their subterms are then given such types. The recursion itself works on untyped expressions: {name kernelToHomQ}`kernelToHomQ` gives the typed view of the translation of a subterm, assuming that the carriers of its source and target are those of {name homCarrier}`homCarrier`.

{docstring kernelToHomQ}

# Memoization

The instances (`MeasurableSpace X`, `IsSFiniteKernel κ`, ...) and the recursively built objects (measurable equivalences, objects of {name SFinKer}`SFinKer`) are memoized in a cache which is reset at the beginning of each transformation. The cache lives in *Eq-Lift*:

{docstring TransformCache}

{docstring resetTransformCache}

{docstring synthInstanceCached}

{docstring memoized}

# Carriers

A measurable space is represented during the lifting by its carrier type and universe level, from which the `MeasurableSpace` instance is obtained through the cache.

{docstring Carrier}

{docstring Carrier.inst}

{docstring Carrier.lift}

{docstring getCarriersFromKernel}

{docstring constructMeasurableEquiv}

After the lifting, all the carriers live in the same universe, in which the translation takes place.

{docstring kernelLevel}

The translation to {name SFinKer}`SFinKer` needs more data about each carrier `X`: the object of {name SFinKer}`SFinKer` it is translated to (`SFinKer.of X`, or a tensor product of such objects when `X` is a product, so that the monoidal tactics see the tensor structure) and the measurable equivalence between the carrier of this object and `X`, which is the argument `ex` of {name ProbabilityTheory.Kernel.toHom}`toHom` and of the translation lemmas. They are computed once per carrier by {name homCarrier}`homCarrier`.

{docstring homCarrier}

{docstring liftCarrier}

In the other direction, the carrier of an object is computed by {name typeOfObj}`typeOfObj`, and its data by {name homCarrier}`homCarrier` again.

{docstring objCarrier}
