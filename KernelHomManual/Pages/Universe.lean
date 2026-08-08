/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import EqLift.Tactic.Lift
import EqLift.Tactic.Unlift
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

The first step in the translation of kernel equalities into categorical equalities is to handle universe levels carefully as categorical expressions occur in a common universe level, while kernels may have carrier spaces in different universe levels.

For instance, consider a category `C` with objects in universe `u` and morphisms in universe `v`:

```lean (name := checkCategory)
variable {C : Type u} [Category.{v, u} C] (c c' : C)
#check C
#check c ⟶ c'
```
```leanOutput checkCategory
C : Type u
```
```leanOutput checkCategory
c ⟶ c' : Type v
```
One can see that the objects of the category are terms of `C : Type u`, and the morphisms are terms of `c ⟶ c' : Type v`

In the context of kernel equalities, we often have kernels where the carrier spaces have different universe levels:

```lean (name := checkKernel)
variable {X : Type x} {Y : Type y} [MeasurableSpace X] [MeasurableSpace Y]
#check Kernel X Y
```
```leanOutput checkKernel
Kernel X Y : Type (max x y)
```

Here, `Kernel X Y` has a universe level that depends on the universe levels of `X` and `Y`: {name Level.max}`max` `x y`.

The counterpart of `Kernel X Y` in the {name SFinKer}`SFinKer` category would be `SFinKer.of X ⟶ SFinKer.of Y`. However, it fails to typecheck as `X` and `Y` have different universe levels:

```lean +error (name := checkSFinKer)
#check SFinKer.of X ⟶ SFinKer.of Y
```
```leanOutput checkSFinKer
Application type mismatch: The argument
  Y
has type
  Type y
of sort `Type (y + 1)` but is expected to have type
  Type x
of sort `Type (x + 1)` in the application
  @SFinKer.of Y
```

To solve this issue, one can manually lift the carrier spaces to a common universe level using {name ULift}`ULift`:

```lean
#check SFinKer.of (ULift.{max x y} X) ⟶ SFinKer.of (ULift Y)
```

In this setting, both `ULift X` and `ULift Y` have the same universe level, allowing the expression to typecheck correctly, as a morphism in {name SFinKer}`SFinKer.{max x y}`.

To translate an equality of kernels into an equality of morphisms in {name SFinKer}`SFinKer`, the first step is to lift all kernels' carrier spaces to a common universe level, using the {name MeasurableEquiv.ulift}`ulift` measurable equivalence. However, determining this common universe level requires care.

One might naively take the universe level of the equality's result (left or right-hand side), but this can fail. Consider the following example:

```lean (name := checkComposition)
variable {Z : Type z} [MeasurableSpace Z] {κ : Kernel X Y} {η : Kernel Z X}
#check κ ∘ₖ η
#check Kernel Z Y
```
```leanOutput checkComposition
κ ∘ₖ η : Kernel Z Y
```
```leanOutput checkComposition
Kernel Z Y : Type (max z y)
```

The type of the composition `κ ∘ₖ η` has universe level {name Level.max}`max` `y z`. The {name SFinKer}`SFinKer` counterpart of this expression would be `η.hom ≫ κ.hom`, where `Kernel.hom` would represent the translation of a kernel into a morphism in {name SFinKer}`SFinKer`. However, to transform `κ` and `η` into morphisms, we need to lift their carrier space `X` (along with `Y` and `Z`) to a common level. If we naively try to lift `X` to only {name Level.max}`max` `y z`, it is impossible because `x` might be larger than {name Level.max}`max` `y z`: we cannot lift a type from a larger universe to a smaller one.

The correct approach is to *lift all carrier spaces to the maximum universe level of every space in the entire expression*, which is {name Level.max}`max` `x y z` in this example. This includes spaces that may "disappear" in the type of the final expression but still need consistent lifting.

To automate this, the {name EqLift}`lift_eq` tactic computes the maximum universe level of all carrier spaces in the kernel expression through the {name collectExprUniverses}`collectExprUniverses` function, and lifts all carrier spaces to this level using {name MeasurableEquiv.ulift}`ulift`. One can then translate the lifted kernel expression into a categorical expression in {name SFinKer}`SFinKer` without worrying about universe inconsistencies.

The {name collectExprUniverses}`collectExprUniverses` function has the following type signature:

{docstring collectExprUniverses}

The {name EqLift}`lift_eq` tactic is not confined to kernel expressions alone. Thanks to its modular design, it can be extended to other kinds of expressions, using the operators and primitives specific to that type. It is thus a general-purpose tactic for raising expressions to a shared universe level, and can be applied in other settings where universe levels need to be reconciled. It is available as a standalone project on [GitHub](https://github.com/gaetanserre/EqLift). The reverse tactic, {name EqUnlift}`unlift_eq`, is also included; it carries out the opposite operation of {name EqLift}`lift_eq`, restoring a lifted expression to its original universe levels.

{docstring EqLift}

{docstring EqUnlift}
