/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import EqLift.Tactic.Kernel.Utils
public import KernelHom.Kernel.Hom

/-!
# Kernel transformation utilities

Explicit constructors for the objects and morphisms of `SFinKer` used by the `kernel_hom` and
`hom_kernel` tactics. The applications are built directly (`mkAppN` with explicit universe levels
and cached instances) instead of going through `mkAppM`.

## Main declarations

* `unfoldKernelOp`: unfolds `Kernel.prod` and `Kernel.compProd`.
* `SFinKerInsts`: the category-theoretic instances of `SFinKer.{u}`.
* `computeSFinkerOf`, `idME`: the object of `SFinKer` associated with a measurable space, and the
  identity measurable equivalence, recursively on products (memoized).
* `mkCatComp`, `mkTensorHom`, ...: explicit constructors of morphisms.
-/

public meta section

open Lean Meta ProbabilityTheory CategoryTheory

/-- Unfold kernel operations in an expression. -/
def unfoldKernelOp (e : Expr) : MetaM Expr := do
  let names := (.empty |> NameSet.insert <| ``Kernel.prod) |> NameSet.insert <| ``Kernel.compProd
  transform e (post := fun e => do
    let e' ← deltaExpand e names.contains
    let e' ← Core.betaReduce e'
    return .done e')

/-- The `IsSFiniteKernel` instance of a kernel (cached). -/
def sfiniteInst (X Y : Carrier) (κ : Expr) : MetaM Expr := do
  synthInstanceCached <| mkAppN (mkConst ``IsSFiniteKernel [X.lvl, Y.lvl])
    #[X.type, Y.type, ← X.inst, ← Y.inst, κ]

/-- The category-theoretic instances of `SFinKer.{u}`. -/
structure SFinKerInsts where
  /-- The universe level. -/
  u : Level
  /-- `SFinKer.{u}`. -/
  C : Expr
  /-- `Category SFinKer`. -/
  cat : Expr
  /-- `CategoryStruct SFinKer`. -/
  catStruct : Expr
  /-- `MonoidalCategory SFinKer`. -/
  monoidal : Expr
  /-- `MonoidalCategoryStruct SFinKer`. -/
  monStruct : Expr

/-- The category-theoretic instances of `SFinKer.{u}` (cached). -/
def sfinkerInsts (u : Level) : MetaM SFinKerInsts := do
  let C := mkConst ``SFinKer [u]
  let lvls := [u, u.succ]
  let cat ← synthInstanceCached (mkApp (mkConst ``Category lvls) C)
  return {
    u, C, cat
    catStruct := ← synthInstanceCached (mkApp (mkConst ``CategoryStruct lvls) C)
    monoidal := ← synthInstanceCached (mkApp2 (mkConst ``MonoidalCategory lvls) C cat)
    monStruct := ← synthInstanceCached (mkApp2 (mkConst ``MonoidalCategoryStruct lvls) C cat) }

namespace SFinKerInsts

/-- `SFinKer.of X`. -/
def of (X : Carrier) : MetaM Expr := do
  return mkApp2 (mkConst ``SFinKer.of [X.lvl]) X.type (← X.inst)

/-- `A ⊗ B`. -/
def tensorObj (I : SFinKerInsts) (A B : Expr) : Expr :=
  mkAppN (mkConst ``MonoidalCategoryStruct.tensorObj [I.u, I.u.succ])
    #[I.C, I.cat, I.monStruct, A, B]

/-- `𝟙_ SFinKer`. -/
def tensorUnit (I : SFinKerInsts) : Expr :=
  mkAppN (mkConst ``MonoidalCategoryStruct.tensorUnit [I.u, I.u.succ]) #[I.C, I.cat, I.monStruct]

/-- `f ≫ g` with `f : X ⟶ Y` and `g : Y ⟶ Z`. -/
def comp (I : SFinKerInsts) (X Y Z f g : Expr) : Expr :=
  mkAppN (mkConst ``CategoryStruct.comp [I.u, I.u.succ]) #[I.C, I.catStruct, X, Y, Z, f, g]

/-- `𝟙 X`. -/
def id (I : SFinKerInsts) (X : Expr) : Expr :=
  mkAppN (mkConst ``CategoryStruct.id [I.u, I.u.succ]) #[I.C, I.catStruct, X]

/-- `f ⊗ₘ g` with `f : X₁ ⟶ Y₁` and `g : X₂ ⟶ Y₂`. -/
def tensorHom (I : SFinKerInsts) (X₁ Y₁ X₂ Y₂ f g : Expr) : Expr :=
  mkAppN (mkConst ``MonoidalCategoryStruct.tensorHom [I.u, I.u.succ])
    #[I.C, I.cat, I.monStruct, X₁, Y₁, X₂, Y₂, f, g]

/-- `X ◁ f` with `f : Y₁ ⟶ Y₂`. -/
def whiskerLeft (I : SFinKerInsts) (X Y₁ Y₂ f : Expr) : Expr :=
  mkAppN (mkConst ``MonoidalCategoryStruct.whiskerLeft [I.u, I.u.succ])
    #[I.C, I.cat, I.monStruct, X, Y₁, Y₂, f]

/-- `f ▷ Y` with `f : X₁ ⟶ X₂`. -/
def whiskerRight (I : SFinKerInsts) (X₁ X₂ f Y : Expr) : Expr :=
  mkAppN (mkConst ``MonoidalCategoryStruct.whiskerRight [I.u, I.u.succ])
    #[I.C, I.cat, I.monStruct, X₁, X₂, f, Y]

/-- The `ComonObj X` instance (cached). -/
def comonInst (I : SFinKerInsts) (X : Expr) : MetaM Expr :=
  synthInstanceCached (mkAppN (mkConst ``ComonObj [I.u, I.u.succ]) #[I.C, I.cat, I.monoidal, X])

/-- `ε[X]`. -/
def counit (I : SFinKerInsts) (X : Expr) : MetaM Expr := do
  return mkAppN (mkConst ``ComonObj.counit [I.u, I.u.succ])
    #[I.C, I.cat, I.monoidal, X, ← I.comonInst X]

/-- `Δ[X]`. -/
def comul (I : SFinKerInsts) (X : Expr) : MetaM Expr := do
  return mkAppN (mkConst ``ComonObj.comul [I.u, I.u.succ])
    #[I.C, I.cat, I.monoidal, X, ← I.comonInst X]

/-- `(β_ X Y).hom`. -/
def braidingHom (I : SFinKerInsts) (X Y : Expr) : MetaM Expr := do
  let braided ← synthInstanceCached
    (mkAppN (mkConst ``BraidedCategory [I.u, I.u.succ]) #[I.C, I.cat, I.monoidal])
  let iso := mkAppN (mkConst ``BraidedCategory.braiding [I.u, I.u.succ])
    #[I.C, I.cat, I.monoidal, braided, X, Y]
  return mkAppN (mkConst ``Iso.hom [I.u, I.u.succ])
    #[I.C, I.cat, I.tensorObj X Y, I.tensorObj Y X, iso]

end SFinKerInsts

/-- Compute the `SFinKer` object corresponding to a measurable space `X : Type xLvl`, decomposing
products into tensor products and `PUnit` into the monoidal unit (memoized). -/
partial def computeSFinkerOf (X : Expr) (xLvl : Level) : MetaM Expr := do
  let res ← memoized `computeSFinkerOf X do
    match X.getAppFn with
    | Expr.const ``PUnit _ | Expr.const ``Unit _ => return #[(← sfinkerInsts xLvl).tensorUnit]
    | Expr.const ``Prod [xLvl, yLvl] =>
      let args := X.getAppArgs
      let I ← sfinkerInsts xLvl
      return #[I.tensorObj (← computeSFinkerOf args[0]! xLvl) (← computeSFinkerOf args[1]! yLvl)]
    | _ => return #[← SFinKerInsts.of ⟨X, xLvl⟩]
  return res[0]!

/-- The measurable equivalence `X ≃ᵐ X`, built recursively on products so that it matches the
decomposition of `computeSFinkerOf` (memoized). -/
partial def idME (X : Expr) (xLvl : Level) : MetaM Expr := do
  let res ← memoized `idME X do
    match X.getAppFn with
    | Expr.const ``Prod [xLvl, yLvl] =>
      let args := X.getAppArgs
      let X₁ := args[0]!
      let X₂ := args[1]!
      return #[mkAppN (mkConst ``MeasurableEquiv.prodCongr [xLvl, xLvl, yLvl, yLvl])
        #[X₁, X₁, X₂, X₂, ← Carrier.inst ⟨X₁, xLvl⟩, ← Carrier.inst ⟨X₁, xLvl⟩,
          ← Carrier.inst ⟨X₂, yLvl⟩, ← Carrier.inst ⟨X₂, yLvl⟩,
          ← idME X₁ xLvl, ← idME X₂ yLvl]]
    | Expr.const ``PUnit [l] | Expr.const ``Unit [l] =>
      let l ← match l with
        | Level.succ l => pure l
        | _ => throwError "Expected a successor level for PUnit/Unit, got: {l}."
      return #[mkConst ``MeasurableEquiv.punit [l, l]]
    | _ => return #[mkApp2 (mkConst ``MeasurableEquiv.refl [xLvl]) X (← Carrier.inst ⟨X, xLvl⟩)]
  return res[0]!

/-- A carrier `X` together with its `MeasurableSpace` instance, its object `obj` in `SFinKer` and
the measurable equivalence `equiv : obj ≃ᵐ X`. -/
structure HomCarrier extends Carrier where
  /-- The `MeasurableSpace` instance. -/
  inst : Expr
  /-- The object of `SFinKer`. -/
  obj : Expr
  /-- The measurable equivalence `obj ≃ᵐ X`. -/
  equiv : Expr

/-- Build the `HomCarrier` of a carrier. -/
def HomCarrier.mk' (X : Carrier) : MetaM HomCarrier := do
  let inst ← X.inst
  let obj ← computeSFinkerOf X.type X.lvl
  let equiv ← idME X.type X.lvl
  return { X with inst, obj, equiv }

instance : Coe HomCarrier Carrier := ⟨HomCarrier.toCarrier⟩

/-- The `IsSFiniteKernel` instance of `κ : Kernel X Y` (cached). -/
def HomCarrier.sfinite (X Y : HomCarrier) (κ : Expr) : MetaM Expr :=
  sfiniteInst X Y κ

/-- The carriers and their `MeasurableSpace` instances: `X Y ... [mX] [mY] ...`. -/
def typeInstArgs (cs : Array HomCarrier) : Array Expr :=
  cs.map (·.type) ++ cs.map (·.inst)

/-- The objects of `SFinKer` and the measurable equivalences: `SX SY ... ex ey ...`. -/
def objEquivArgs (cs : Array HomCarrier) : Array Expr :=
  cs.map (·.obj) ++ cs.map (·.equiv)

/-- The arguments shared by the translation lemmas for carriers `X Y ...`:
`X Y ... [mX] [mY] ... SX SY ... ex ey ...`. -/
def homLemmaArgs (cs : Array HomCarrier) : Array Expr :=
  typeInstArgs cs ++ objEquivArgs cs

/-- `κ.hom (ex := ex) (ey := ey) : SX ⟶ SY`. -/
def mkHom (X Y : HomCarrier) (κ : Expr) : MetaM Expr := do
  return mkAppN (mkConst ``Kernel.hom [X.lvl, Y.lvl, X.lvl])
    (homLemmaArgs #[X, Y] ++ #[κ, ← X.sfinite Y κ])

end
