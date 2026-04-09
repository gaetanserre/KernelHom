/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import KernelHom.Tactic.Hom.Universe
import Mathlib.Probability.Kernel.Category.SFinKer
import VersoManual

open Verso.Genre Manual Verso.Genre.Manual.InlineLean Verso.Code.External
open CategoryTheory ProbabilityTheory

set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option pp.rawOnError true
set_option verso.code.warnLineLength 100
set_option verso.exampleProject "."
set_option verso.exampleModule "KernelHom.Tactic.Hom.Universe"

#doc (Manual) "Universe handling" =>
%%%
htmlSplit := .never
%%%

To translate kernel equalities into categorical equalities, one needs to handle universe levels carefully as categorical expressions occur in a common universe level:

```lean
variable {C : Type u} [Category.{v, u} C] (c c' : C)
#check C
#check c ⟶ c'
```
One can see that the objects of the category `C` live in `Type u`, while the morphisms live in `Type v`.

In the context of kernel equalities, we often have kernels where the carrier spaces live in different universe levels:

```lean
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
#check Kernel X Y
```
Here, `Kernel X Y` lives in a universe level that depends on the universe levels of `X` and `Y`.

The counterpart of `Kernel X Y` in the [`SFinKer`](doc/Mathlib/Probability/Kernel/Category/SFinKer.html#SFinKer) category would be `SFinKer.of X ⟶ SFinKer.of Y`. However, it fails to typecheck as `X` and `Y` live in different universe levels:

```lean +error
#check SFinKer.of X ⟶ SFinKer.of Y
```

To solve this issue, one can manually lift the carrier spaces to a common universe level using [`ULift`](doc/Init/Prelude.html#ULift):
```lean
#check SFinKer.of (ULift.{max u_1 u_2} X) ⟶ SFinKer.of (ULift Y)
```
In this setting, both `ULift X` and `ULift Y` live in the same universe level, allowing the expression to typecheck correctly.

However, manually uniformizing universe levels can be cumbersome when dealing with expressions involving multiple kernels of different carrier spaces. To this end, we designed the {anchorTerm collectExprUniverses}`collectExprUniverses` function, which recursively traverses an expression and collects all universe levels found. This allows us to automatically determine the minimum common universe level for which all carrier spaces of the kernels involved in a given expression can be lifted to (most likely the maximum of all universe levels encountered), and uniformly lift them to that level during the translation process.

{docstring collectExprUniverses}
