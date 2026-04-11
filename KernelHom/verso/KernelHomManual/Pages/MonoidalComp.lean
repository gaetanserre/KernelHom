/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import KernelHom.Kernel.MonoidalComp
import VersoManual

open Verso.Genre Manual Verso.Genre.Manual.InlineLean Verso.Code.External MeasurableCoherence

set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "Kernelized monoidal composition" =>
%%%
htmlSplit := .never
shortTitle := "Monoidal composition"
%%%

The translation of kernels to morphisms in the {name SFinKer}`SFinKer` category allows to adapt the “{name CategoryTheory.monoidalComp}`⊗≫`” monoidal composition for kernels. The {name MeasurableCoherence}`MeasurableCoherence` class witnesses measurable equivalences between types, enabling an instance of categorical {name monoidalCoherence}`MonoidalCoherence` that makes the kernelized monoidal composition (noted “{name ProbabilityTheory.Kernel.monoComp}`⊗≫ₖ`”) possible.

# Measurable Coherence

The {name MeasurableCoherence}`MeasurableCoherence` class witnesses the existence of measurable equivalences between two measurable spaces. It acts as a kernel-level counterpart to the categorical {name monoidalCoherence}`MonoidalCoherence` class:

{docstring MeasurableCoherence}

This class enables an instance of {name CategoryTheory.MonoidalCoherence}`MonoidalCoherence` between {name SFinKer}`SFinKer` objects at a common universe level via the {name monoidalCoherence}`monoidalCoherence` function, using measurable equivalences from the original types.

{docstring monoidalCoherence}

This allows to bridge the gap between the notion of measurable equivalence and the categorical notion of monoidal coherence, enabling the use of categorical machinery for kernel compositions.

# Monoidal Composition of Kernels

The kernelized monoidal composition “{name ProbabilityTheory.Kernel.monoComp}`⊗≫ₖ`” is defined by composing two kernels while automatically handling measurable equivalences through the categorical framework:

1. *Transport to {name SFinKer}`SFinKer`*: Both kernels are translated to morphisms in the {name SFinKer}`SFinKer` category using the {name ProbabilityTheory.Kernel.hom}`hom` function, which lifts carrier spaces to a common universe level.

1. *Categorical composition*: The categorical monoidal composition “{name CategoryTheory.monoidalComp}`⊗≫`” is applied to the resulting morphisms in {name SFinKer}`SFinKer`, which automatically inserts the necessary associators and unitors.

1. *Transport back to kernels*: The result is translated back to a kernel using the {name ProbabilityTheory.Kernel.fromHom}`fromHom` function.
