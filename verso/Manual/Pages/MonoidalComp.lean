/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import VersoManual

open Verso.Genre Manual Verso.Genre.Manual.InlineLean Verso.Code.External

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100
set_option verso.exampleProject "../"
set_option verso.exampleModule "KernelHom.Kernel.MonoidalComp"

#doc (Manual) "Kernelized monoidal composition" =>
%%%
htmlSplit := .never
shortTitle := "Monoidal composition"
%%%

The translation of kernels to morphisms in the [`SFinKer`](doc/Mathlib/Probability/Kernel/Category/SFinKer.html#SFinKer) category allows us to adapt the “`⊗≫`” monoidal composition for kernels. The {anchorTerm MeasurableCoherence}`MeasurableCoherence` class witnesses measurable equivalences between types, enabling an instance of categorical {anchorTerm monoidalCoherence}`MonoidalCoherence` that makes the kernelized monoidal composition (noted “`⊗≫ₖ`”) possible.

# Measurable Coherence

The {anchorTerm MeasurableCoherence}`MeasurableCoherence` class witnesses the existence of measurable equivalences between two measurable spaces. It acts as a kernel-level counterpart to the categorical {anchorTerm monoidalCoherence}`MonoidalCoherence` class:

```anchor MeasurableCoherence
class MeasurableCoherence (X Y : Type*) [MeasurableSpace X] [MeasurableSpace Y] where
  /-- A measurable equivalence between `X` and `Y`. -/
  miso : X ≃ᵐ Y
```

This class enables an instance of {anchorTerm monoidalCoherence}`MonoidalCoherence` between [`SFinKer`](doc/Mathlib/Probability/Kernel/Category/SFinKer.html#SFinKer) objects at a common universe level via the {anchorTerm monoidalCoherence}`monoidalCoherence` function, using measurable equivalences from the original types.

This allows us to bridge the gap between the notion of measurable equivalence and the categorical notion of monoidal coherence, enabling the use of categorical machinery for kernel compositions.

# Monoidal Composition of Kernels

The kernelized monoidal composition “`⊗≫ₖ`” is defined by composing two kernels while automatically handling measurable equivalences through the categorical framework:

1. *Transport to [`SFinKer`](doc/Mathlib/Probability/Kernel/Category/SFinKer.html#SFinKer)*: Both kernels are translated to morphisms in the [`SFinKer`](doc/Mathlib/Probability/Kernel/Category/SFinKer.html#SFinKer) category using the [`hom`](doc/KernelHom/Kernel/Hom.html#ProbabilityTheory.Kernel.hom) function, which lifts carrier spaces to a common universe level.

1. *Categorical composition*: The categorical monoidal composition “`⊗≫`” is applied to the resulting morphisms in [`SFinKer`](doc/Mathlib/Probability/Kernel/Category/SFinKer.html#SFinKer), which automatically inserts the necessary associators and unitors.

1. *Transport back to kernels*: The result is translated back to a kernel using the [`fromHom` ](doc/KernelHom/Kernel/Hom.html#ProbabilityTheory.Kernel.fromHom) function.
