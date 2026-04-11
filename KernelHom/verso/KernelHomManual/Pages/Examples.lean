/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import KernelHom.Tests.Examples
import KernelHom.verso.Tools.VersoKernelDiagram
import KernelHom.verso.Tools.LeanDecl
import VersoManual

open Verso.Genre Manual Verso.Genre.Manual.InlineLean Verso.Code.External Mathlib.Tactic

open ProbabilityTheory Kernel

open scoped CategoryTheory.ComonObj

set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option pp.rawOnError true
set_option verso.code.warnLineLength 100
set_option verso.exampleProject "."
set_option verso.exampleModule "KernelHom.Tests.Examples"

#doc (Manual) "Usage and examples" =>
%%%
htmlSplit := .never
%%%

# Usage

To use *Kernel-Hom*, add the following to your `lakefile.toml`:
```
[[require]]
name = "kernelhom"
git = "https://github.com/gaetanserre/KernelHom.git"
```

or to your `lakefile.lean`:
```
require kernelhom from git "https://github.com/gaetanserre/KernelHom" @ "main"
```

Then, in your Lean files, you can import the library with:

```
import KernelHom
```

*Tactics*

The library provides several tactics for working with s-finite kernels equalities. The main tactics are:
- {name kernelHom}`kernel_hom`: Transforms a s-finite kernel equality into an equality in the {name SFinKer}`SFinKer` monoidal category.

- {name homKernel}`hom_kernel`: The inverse of {name kernelHom}`kernel_hom`, transforms an equality in {name SFinKer}`SFinKer` back into a kernel equality.

- {name kernelMonoidal}`kernel_monoidal`: Applies the {name Monoidal.monoidal}`monoidal` tactic to a s-finite kernel equality.

- {name kernelCoherence}`kernel_coherence`: Applies the {name Coherence.coherence}`coherence` tactic to a s-finite kernel equality.

Basically, whenever you have a equality of s-finite kernels that you want to simplify, you can apply {name kernelHom}`kernel_hom` to transform it into a categorical equality, try applying categorical tactics, simps, or manually manipulate it, and then apply {name homKernel}`hom_kernel` to get back to a kernel equality if needed. The built-in helpers {name kernelMonoidal}`kernel_monoidal` and {name kernelCoherence}`kernel_coherence` directly apply categorical tactics to kernels without needing to manually invoke the translation tactic.

*Kernel diagrams*

The library also provides the {name kernelDiagram}`kernel_diagram` command, which generates string diagrams for kernel expressions. This is an adaptation of the {name Widget.stringDiagram}`string_diagram` command, where s-finite kernels are represented as morphisms using {name kernelHom}`kernel_hom`. This provides a visual representation of kernel compositions and transformations, aiding intuition and understanding. The use of this command is similar to {name Widget.stringDiagram}`string_diagram`:

```lean
#kernel_diagram deterministic_comp_copy
```

```VersoTools.kernelDiagram
deterministic_comp_copy
```

# Examples

These tactics are particularly useful when dealing with compositions and parallel compositions of kernels. The following examples are taken from the file [`KernelLemmas.lean`](doc/Mathlib/Probability/Kernel/Composition/KernelLemmas.html) and illustrate how the tactics can be used to drastically simplify the proofs of kernel equalities.

- {name parallelComp_id_left_comp_parallelComp}`parallelComp_id_left_comp_parallelComp`

```VersoTools.leanDecl
ProbabilityTheory.Kernel.parallelComp_id_left_comp_parallelComp₀
```

```VersoTools.kernelDiagram
ProbabilityTheory.Kernel.parallelComp_id_left_comp_parallelComp_diag
```

- {name parallelComp_id_right_comp_parallelComp}`parallelComp_id_right_comp_parallelComp`

```VersoTools.leanDecl
ProbabilityTheory.Kernel.parallelComp_id_right_comp_parallelComp₀
```

```VersoTools.kernelDiagram
ProbabilityTheory.Kernel.parallelComp_id_right_comp_parallelComp_diag
```

- {name parallelComp_comp_parallelComp}`parallelComp_comp_parallelComp`

```VersoTools.leanDecl
ProbabilityTheory.Kernel.parallelComp_comp_parallelComp₀
```

```VersoTools.kernelDiagram
ProbabilityTheory.Kernel.parallelComp_comp_parallelComp₀
```

- {name parallelComp_comp_prod}`parallelComp_comp_prod`

```VersoTools.leanDecl
ProbabilityTheory.Kernel.parallelComp_comp_prod₀
```

```VersoTools.kernelDiagram
ProbabilityTheory.Kernel.parallelComp_comp_prod₀
```

- {name swap_parallelComp}`swap_parallelComp`

  Object of the symmetric category are also handled by the tactic, such as {name ProbabilityTheory.Kernel.swap}`Kernel.swap` that is translated to the right braiding of {name SFinKer}`SFinKer`.


```VersoTools.leanDecl
ProbabilityTheory.Kernel.swap_parallelComp₀
```

```VersoTools.kernelDiagram
ProbabilityTheory.Kernel.swap_parallelComp_diag
```

- {name deterministic_comp_copy}`deterministic_comp_copy`

  The categorical counterpart of {name ProbabilityTheory.Kernel.deterministic}`Kernel.deterministic` are automatically treated as {name CategoryTheory.Deterministic}`Deterministic` morphisms.

```VersoTools.leanDecl
ProbabilityTheory.Kernel.deterministic_comp_copy₀
```

```VersoTools.kernelDiagram
ProbabilityTheory.Kernel.deterministic_comp_copy₀
```

```VersoTools.leanDecl
ProbabilityTheory.Kernel.discard_comp_deterministic
```

```VersoTools.kernelDiagram
ProbabilityTheory.Kernel.discard_comp_deterministic
```
