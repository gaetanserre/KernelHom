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
open Lean

set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

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
One can see that the objects of the category are terms of `C : Type u`, and the morphisms are terms of `c ⟶ c' : Type v`

In the context of kernel equalities, we often have kernels where the carrier spaces have different universe levels:

```lean
variable {X : Type x} {Y : Type y} [MeasurableSpace X] [MeasurableSpace Y]
#check Kernel X Y
```
Here, `Kernel X Y` has a universe level that depends on the universe levels of `X` and `Y`: {name Level.max}`max` `x y`.

The counterpart of `Kernel X Y` in the {name SFinKer}`SFinKer` category would be `SFinKer.of X ⟶ SFinKer.of Y`. However, it fails to typecheck as `X` and `Y` have different universe levels:

```lean +error
#check SFinKer.of X ⟶ SFinKer.of Y
```

To solve this issue, one can manually lift the carrier spaces to a common universe level using {name ULift}`ULift`:
```lean
#check SFinKer.of (ULift.{max x y} X) ⟶ SFinKer.of (ULift Y)
```
In this setting, both `ULift X` and `ULift Y` have the same universe level, allowing the expression to typecheck correctly, as a morphism in {name SFinKer}`SFinKer.{max x y}`.

To translate an equality of kernels into an equality of morphisms in {name SFinKer}`SFinKer`, all kernels must be translated to morphisms in {name SFinKer}`SFinKer` by lifting their carrier spaces to a common universe level, using the {name MeasurableEquiv.ulift}`ulift` measurable equivalence. However, determining this common universe level requires care.

One might naively take the universe level of the equality's result (left or right-hand side), but this can fail. Consider the following example:

```lean
variable {Z : Type z} [MeasurableSpace Z] {κ : Kernel X Y} {η : Kernel Z X}
#check κ ∘ₖ η
#check Kernel Z Y
```
The type of the composition `κ ∘ₖ η` has universe level {name Level.max}`max` `y z`. However, to transform `κ` into a morphism in {name SFinKer}`SFinKer`, we must lift its carrier space `X` (along with `Y`) to a common level. If one naively tries to lift `X` to only {name Level.max}`max` `y z`, it is impossible because `x` might be larger than {name Level.max}`max` `y z`: we cannot lift a type from a larger universe to a smaller one.

The correct approach is to *lift all carrier spaces to the maximum universe level of every space in the entire expression*, which is {name Level.max}`max` `x y z` in this example. This includes spaces that may "disappear" in the final result but still need consistent lifting.

To automate this, the {name collectExprUniverses}`collectExprUniverses` function recursively collects all universe levels found in an expression. This allows us to determine the appropriate common universe level and uniformly lift all carrier spaces to it.

{docstring collectExprUniverses}
