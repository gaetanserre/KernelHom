/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import KernelHom.Kernel.MonoidalComp
public import KernelHom.Tactic.Utils
public import Lean.Elab.Tactic.Location
public import EqLift.Tactic.Kernel.KernelLift

/-!
# `kernel_hom` tactic

This file implements the `kernel_hom` tactic, which transforms equalities of
kernels into equivalent equalities in the monoidal category.

## Main declarations

* `transformKernelToHom`: recursive translation from kernel expressions to
  categorical morphism expressions.
* `mkHomCongrProof`: construction of the equivalence proof used by the tactic.
* `HomEquality`: core implementation of `kernel_hom` on an equality.
* `kernel_hom`: user-facing tactic (with location support).
-/

public meta section

open Lean Elab Tactic Meta CategoryTheory Parser.Tactic ProbabilityTheory MonoidalCategory
open ProbabilityTheory.Kernel

/-- Check if a kernel expression corresponds to a left or right whisker. -/
def checkWhiskers (κ : Expr) (offset : Nat) : MetaM Bool := do
  let κ := κ.consumeMData
  let args := κ.getAppArgs
  let idKernel := args[args.size - offset]!
  if !idKernel.isAppOf ``Kernel.id then
    return false
  else return true

/-- Check if a kernel expression corresponds to a left whisker. -/
def checkWhiskerLeft (κ : Expr) : MetaM Bool := checkWhiskers κ 2

/-- Check if a kernel expression corresponds to a right whisker. -/
def checkWhiskerRight (κ : Expr) : MetaM Bool := checkWhiskers κ 1

/-- Given a whisker `e = Kernel.id ∥ₖ κ` (left) or `e = κ ∥ₖ Kernel.id` (right) with
`κ : Kernel X Y` and `Kernel.id : Kernel Z Z`, return the carriers `Z X Y` and `κ`. -/
def whiskerData (e : Expr) (left : Bool) : MetaM (Carrier × Carrier × Carrier × Expr) := do
  let (src, tgt, _, _) ← getTypesFromKernel e
  let prodArgs (P : Expr) : MetaM (Carrier × Carrier) := do
    match P.getAppFn with
    | Expr.const ``Prod [l₁, l₂] =>
      let args := P.getAppArgs
      return (⟨args[0]!, l₁⟩, ⟨args[1]!, l₂⟩)
    | _ => throwError "Expected a product type, got: {P}."
  let (s₁, s₂) ← prodArgs src
  let (t₁, t₂) ← prodArgs tgt
  let args := e.getAppArgs
  if left then
    return (s₁, s₂, t₂, args[args.size - 1]!)
  else
    return (s₂, s₁, t₁, args[args.size - 2]!)

/-- Check if a kernel expression corresponds to a left or right unitor. -/
def checkUnitors (κ : Expr) (offset : Nat) (prod : Name) : MetaM Bool := do
  let κ := κ.consumeMData
  if !κ.isAppOf ``Kernel.map then
    return false
  let args := κ.getAppArgs
  let fn := args[args.size - 1]!
  let idKernel := args[args.size - 2]!
  if !fn.isAppOf prod then
    return false
  if !idKernel.isAppOf ``Kernel.id then
    return false
  let (src, _, _) ← getTypesFromKernel κ
  match src.getAppFn with
  | Expr.const ``Prod _ =>
    let args := src.getAppArgs
    if args.size < 2 then
      return false
    let punit? := args[offset]!
    match punit?.getAppFn with
    | Expr.const ``PUnit _ | Expr.const ``Unit _ => return true
    | _ => return false
  | _ => return false

/-- Check if a kernel expression corresponds to a left unitor. -/
def checkLeftUnitor (κ : Expr) : MetaM Bool := checkUnitors κ 0 ``Prod.snd

/-- Check if a kernel expression corresponds to a right unitor. -/
def checkRightUnitor (κ : Expr) : MetaM Bool := checkUnitors κ 1 ``Prod.fst

/-- Construct the left or right unitor morphism. -/
def constructUnitors (X ex₀ : Expr) (xLvl y₀Lvl punitLvl : Level) (offset : Nat) :
    MetaM (Expr × Expr) := do
  let left ← if offset == 0 then pure true
    else if offset == 1 then pure false
    else throwError "Invalid offset for unitors."
  let SX ← computeSFinkerOf X xLvl
  let unitor ← if left then mkAppM ``leftUnitor #[SX]
    else mkAppM ``rightUnitor #[SX]
  let unitor_hom_const :=
    if left then mkConst ``leftUnitor_hom [xLvl, xLvl, y₀Lvl, punitLvl]
    else mkConst ``rightUnitor_hom [xLvl, xLvl, y₀Lvl, punitLvl]
  let unitor_hom_proof ←
    if left then mkAppM' unitor_hom_const #[SX, ← idME X xLvl, ex₀]
    else mkAppM' unitor_hom_const #[SX, ← idME X xLvl, ex₀]
  return (← mkAppM ``Iso.hom #[unitor], unitor_hom_proof)

/-- Check if a kernel expression corresponds to an associator morphism or its inverse. -/
def checkAssociator (κ : Expr) (hom : Bool) : MetaM Bool := do
  let κ := κ.consumeMData
  if !κ.isAppOf ``Kernel.deterministic then
    return false
  let args := κ.getAppArgs
  let fn := args[args.size - 2]!
  if !fn.isAppOf ``DFunLike.coe then
    return false
  let fn := fn.getAppArgs[fn.getAppApps.size - 1]!
  if hom then
    if !fn.isAppOf ``MeasurableEquiv.prodAssoc then
      return false
  else
    if !fn.isAppOf ``MeasurableEquiv.symm then
      return false
    let innerFn := fn.getAppArgs[fn.getAppArgs.size - 1]!
    if !innerFn.isAppOf ``MeasurableEquiv.prodAssoc then
      return false
  return true

/-- Check if a kernel expression corresponds to an associator morphism. -/
def checkAssociatorHom (κ : Expr) : MetaM Bool := checkAssociator κ true

/-- Check if a kernel expression corresponds to an inverse associator morphism. -/
def checkAssociatorInv (κ : Expr) : MetaM Bool := checkAssociator κ false

/-- Get the types and universe levels from a expression of the form `X × Y × Z`. -/
def getTypesFromThreeProds (prod : Expr) :
    MetaM (Expr × Expr × Expr × Level × Level × Level) := do
  match prod.getAppFn with
  | Expr.const ``Prod univs =>
    let X := prod.getAppArgs[0]!
    match prod.getAppArgs[1]!.getAppFn with
    | Expr.const ``Prod univs_right =>
      let Y := prod.getAppArgs[1]!.getAppArgs[0]!
      let Z := prod.getAppArgs[1]!.getAppArgs[1]!
      return (X, Y, Z, univs[0]!, univs_right[0]!, univs_right[1]!)
    | _ => throwError "Expected a product of two types, got: {prod.getAppArgs[1]!}."
  | _ => throwError "Expected a product of three types, got: {prod}."

/-- Get the measurable equivalences from a product of three measurable equivalences. -/
def getMEFromThreeProds (me_prod : Expr) :
    MetaM (Expr × Expr × Expr) := do
  match me_prod.getAppFn with
  | Expr.const ``MeasurableEquiv.prodCongr _ =>
    let args := me_prod.getAppArgs
    let ex := args[args.size - 2]!
    let right := args[args.size - 1]!
    match right.getAppFn with
    | Expr.const ``MeasurableEquiv.prodCongr _ =>
      let rightArgs := right.getAppArgs
      let ey := rightArgs[rightArgs.size - 2]!
      let ez := rightArgs[rightArgs.size - 1]!
      return (ex, ey, ez)
    | _ => throwError "Expected a product of two measurable equivalences, got: {right}."
  | _ => throwError "Expected a product of three measurable equivalences, got: {me_prod}."

/-- Construct the associator morphism or its inverse. -/
def constructAssociator (left right ex₀ ey₀ ez₀ : Expr) (hom : Bool) :
    MetaM (Expr × Expr) := do
  let (X, Y, Z, xLvl, yLvl, zLvl) ← if hom then getTypesFromThreeProds right
    else getTypesFromThreeProds left
  let SX ← computeSFinkerOf X xLvl
  let SY ← computeSFinkerOf Y yLvl
  let SZ ← computeSFinkerOf Z zLvl
  let associator ← mkAppM ``MonoidalCategory.associator #[SX, SY, SZ]
  let lemmaArgs := #[SX, SY, SZ, ← idME X xLvl, ← idME Y yLvl, ← idME Z zLvl, ex₀, ey₀, ez₀]
  let associator_hom_proof ← mkAppM (if hom then ``associator_hom else ``associator_inv) lemmaArgs
  return (← mkAppM (if hom then ``Iso.hom else ``Iso.inv) #[associator], associator_hom_proof)

/-- Construct the associator morphism. -/
def constructAssociatorHom (left right ex₀ ey₀ ez₀ : Expr) :=
  constructAssociator left right ex₀ ey₀ ez₀ true

/-- Construct the inverse associator morphism. -/
def constructAssociatorInv (left right ex₀ ey₀ ez₀ : Expr) :=
  constructAssociator left right ex₀ ey₀ ez₀ false

/-- Recursive transformation from kernel expressions to morphism expressions in the `SFinKer`
category. Returns the morphism expression `e'` together with a proof of `e' = e.hom`, built by
congruence from the translation lemmas (`comp_hom`, `parallelComp_hom`, ...). -/
partial def transformKernelToHom (e : Expr) : MetaM (Expr × Expr) := do
  match e.getAppFn with
  | Expr.const ``Kernel.comp _ =>
    let args := e.getAppArgs
    let η := args[args.size - 2]!
    let κ := args[args.size - 1]!
    let (X, Y) ← getCarriersFromKernel η
    let (Z, _) ← getCarriersFromKernel κ
    let (X, Y, Z) := (← HomCarrier.mk' X, ← HomCarrier.mk' Y, ← HomCarrier.mk' Z)
    let I ← sfinkerInsts X.lvl
    let pf := mkAppN (mkConst ``comp_hom [X.lvl, Y.lvl, Z.lvl, I.u])
      (homLemmaArgs #[X, Y, Z] ++
        #[η, κ, ← X.sfinite Y η, ← Z.sfinite X κ])
    let (κ', pκ) ← transformKernelToHom κ
    let (η', pη) ← transformKernelToHom η
    let e' := I.comp Z.obj X.obj Y.obj κ' η'
    let h ← mkCongr (← mkCongrArg e'.appFn!.appFn! pκ) pη
    return (e', ← mkEqTrans h pf)
  | Expr.const ``Kernel.parallelComp _ =>
    if ← checkWhiskerLeft e then
      let (Z, X, Y, κ) ← whiskerData e true
      let (X, Y, Z) := (← HomCarrier.mk' X, ← HomCarrier.mk' Y, ← HomCarrier.mk' Z)
      let I ← sfinkerInsts X.lvl
      let pf := mkAppN (mkConst ``Kernel.whiskerLeft [X.lvl, Y.lvl, Z.lvl, I.u])
        (homLemmaArgs #[X, Y, Z] ++ #[κ, ← X.sfinite Y κ])
      let (κ', pκ) ← transformKernelToHom κ
      let e' := I.whiskerLeft Z.obj X.obj Y.obj κ'
      let h ← mkCongrArg e'.appFn! pκ
      return (e', ← mkEqTrans h pf)
    else if ← checkWhiskerRight e then
      let (Z, X, Y, κ) ← whiskerData e false
      let (X, Y, Z) := (← HomCarrier.mk' X, ← HomCarrier.mk' Y, ← HomCarrier.mk' Z)
      let I ← sfinkerInsts X.lvl
      let pf := mkAppN (mkConst ``Kernel.whiskerRight [X.lvl, Y.lvl, Z.lvl, I.u])
        (homLemmaArgs #[X, Y, Z] ++ #[κ, ← X.sfinite Y κ])
      let (κ', pκ) ← transformKernelToHom κ
      let e' := I.whiskerRight X.obj Y.obj κ' Z.obj
      let h ← mkCongrFun (← mkCongrArg e'.appFn!.appFn! pκ) Z.obj
      return (e', ← mkEqTrans h pf)
    else
      let args := e.getAppArgs
      let κ := args[args.size - 2]!
      let η := args[args.size - 1]!
      let (X, Y) ← getCarriersFromKernel κ
      let (Z, T) ← getCarriersFromKernel η
      let (X, Y, Z, T) :=
        (← HomCarrier.mk' X, ← HomCarrier.mk' Y, ← HomCarrier.mk' Z, ← HomCarrier.mk' T)
      let I ← sfinkerInsts X.lvl
      let pf := mkAppN (mkConst ``parallelComp_hom [X.lvl, Y.lvl, T.lvl, Z.lvl, I.u])
        (typeInstArgs #[X, Y, T, Z] ++ objEquivArgs #[X, Y, Z, T] ++
          #[κ, η, ← Z.sfinite T η, ← X.sfinite Y κ])
      let (κ', pκ) ← transformKernelToHom κ
      let (η', pη) ← transformKernelToHom η
      let e' := I.tensorHom X.obj Y.obj Z.obj T.obj κ' η'
      let h ← mkCongr (← mkCongrArg e'.appFn!.appFn! pκ) pη
      return (e', ← mkEqTrans h pf)
  | Expr.const ``Kernel.id [xLvl] =>
    let X ← HomCarrier.mk' ⟨e.getAppArgs[0]!, xLvl⟩
    let I ← sfinkerInsts xLvl
    return (I.id X.obj, mkAppN (mkConst ``id_hom [xLvl, I.u]) (homLemmaArgs #[X]))
  | Expr.const ``Kernel.discard [xLvl, punitLvl] =>
    let X ← HomCarrier.mk' ⟨e.getAppArgs[0]!, xLvl⟩
    let I ← sfinkerInsts xLvl
    return (← I.counit X.obj,
      mkAppN (mkConst ``counit [xLvl, I.u, punitLvl]) (homLemmaArgs #[X]))
  | Expr.const ``Kernel.copy [xLvl] =>
    let X ← HomCarrier.mk' ⟨e.getAppArgs[0]!, xLvl⟩
    let I ← sfinkerInsts xLvl
    return (← I.comul X.obj, mkAppN (mkConst ``comul [xLvl, I.u]) (homLemmaArgs #[X]))
  | Expr.const ``Kernel.swap [xLvl, yLvl] =>
    let X ← HomCarrier.mk' ⟨e.getAppArgs[0]!, xLvl⟩
    let Y ← HomCarrier.mk' ⟨e.getAppArgs[1]!, yLvl⟩
    let I ← sfinkerInsts xLvl
    return (← I.braidingHom X.obj Y.obj,
      mkAppN (mkConst ``braiding_hom [xLvl, yLvl, I.u]) (homLemmaArgs #[X, Y]))
  | Expr.const ``Kernel.lift [_, y₀Lvl, _] =>
    let (X, Y, xLvl, yLvl) ← getTypesFromKernel e
    let args := e.getAppArgs
    let κ := args[args.size - 1]!
    if ← checkLeftUnitor κ then
      let punitLvl ← match args[0]!.getAppFn with
        | Expr.const ``Prod [punitLvl, _] => pure punitLvl
        | _ => throwError "Expected a product with PUnit as the first component, got {args[0]!}."
      constructUnitors Y args[args.size - 2]! yLvl y₀Lvl punitLvl 0
    else if ← checkRightUnitor κ then
      let punitLvl ← match args[0]!.getAppFn with
        | Expr.const ``Prod [_, punitLvl] => pure punitLvl
        | _ => throwError "Expected a product with PUnit as the second component, got {args[0]!}."
      constructUnitors Y args[args.size - 2]! yLvl y₀Lvl punitLvl 1
    else if ← checkAssociatorHom κ then
      let (ex₀, ey₀, ez₀) ← getMEFromThreeProds args[args.size - 2]!
      constructAssociatorHom X Y ex₀ ey₀ ez₀
    else if ← checkAssociatorInv κ then
      let (ex₀, ey₀, ez₀) ← getMEFromThreeProds args[args.size - 3]!
      constructAssociatorInv X Y ex₀ ey₀ ez₀
    else
      let homExpr ← mkHom (← HomCarrier.mk' ⟨X, xLvl⟩) (← HomCarrier.mk' ⟨Y, yLvl⟩) e
      return (homExpr, ← mkEqRefl homExpr)
  | _ =>
    throwError "Expected a lifted kernel expression, got: {e}."

/-- Given lifted kernels `lhs rhs` and morphisms `lh rh` with proofs `pl : lh = lhs.hom` and
`pr : rh = rhs.hom`, construct a proof of `(lhs = rhs) = (lh = rh)`. -/
def mkHomCongrProof (lhs rhs pl pr : Expr) : MetaM Expr := do
  let (X, Y) ← getCarriersFromKernel lhs
  let (X, Y) := (← HomCarrier.mk' X, ← HomCarrier.mk' Y)
  let hom_congr_proof := mkAppN (mkConst ``hom_congr [X.lvl, Y.lvl, X.lvl]) <|
    homLemmaArgs #[X, Y] ++
      #[lhs, rhs, ← X.sfinite Y lhs, ← X.sfinite Y rhs]
  mkEqTrans (← mkPropExt hom_congr_proof) (← mkEqSymm (← mkEqCongr pl pr))

/-- Transform a kernel equality into an equivalent equality in `SFinKer`, along with a proof of
equivalence. The equality is first lifted to a common universe level using `lift`. -/
def HomEqualityWith (lift : Expr → MetaM (Expr × Expr)) (eq : Expr) : MetaM (Expr × Expr) := do
  let eq ← unfoldKernelOp eq
  let (lifted_expr, lifted_proof) ← lift eq
  let some (_, lhs, rhs) := lifted_expr.eq? | throwError "Expected an equality, got: {lifted_expr}."
  let (lhs_hom, pl) ← transformKernelToHom lhs
  let (rhs_hom, pr) ← transformKernelToHom rhs
  let hom_expr ← mkEq lhs_hom rhs_hom
  let hom_eq_proof ← mkHomCongrProof lhs rhs pl pr
  return (hom_expr, ← mkEqTrans lifted_proof hom_eq_proof)

/-- Transform a kernel equality into an equivalent equality in `SFinKer`, along with a proof of
equivalence. -/
def HomEquality : Expr → MetaM (Expr × Expr) := HomEqualityWith liftEquality

/-- The types of the hypotheses and of the goal at a location. -/
def locationTypes (loc : Location) : TacticM (Array Expr) := withMainContext do
  match loc with
  | .targets hyps target =>
    let types ← hyps.mapM fun h ↦ do (← getFVarId h).getType
    if target then return types.push (← getMainTarget) else return types
  | .wildcard =>
    let types := (← getLCtx).foldl (init := #[]) fun types decl ↦
      if decl.isImplementationDetail then types else types.push decl.type
    return types.push (← getMainTarget)

/-- Transform the kernel equalities at a location into equalities in `SFinKer`. When there are
several of them, they are all lifted to a common universe level (the maximum of their universe
levels), so that the translated equalities live in the same category and can be used together. -/
def HomEqualityAt (loc : Location) : TacticM Unit := do
  let types ← locationTypes loc
  if types.size ≤ 1 then
    return ← applyLocTactic loc HomEquality
  let lvls ← types.foldlM (init := []) fun lvls type ↦ do
    try return lvls ++ (← collectEqUniverses (← unfoldKernelOp type)) catch _ => return lvls
  if lvls.isEmpty then
    return ← applyLocTactic loc HomEquality
  applyLocTactic loc <| HomEqualityWith (liftEqualityWithLevel (← computeMaxLevel lvls))

/-- The `kernel_hom` tactic transforms a kernel equality to an equivalent equality in
the category of measurable spaces and s-finite kernels.

The tactic supports location specifiers like `rw` or `simp`:
* `kernel_hom` — applies to the goal
* `kernel_hom at h` — applies to hypothesis `h`
* `kernel_hom at h₁ h₂` — applies to multiple hypotheses
* `kernel_hom at h ⊢` — applies to hypothesis `h` and the goal
* `kernel_hom at *` — applies to all hypotheses and the goal

All the equalities are lifted to a common universe level, so that the resulting categorical
equalities live in the same category and can be used to rewrite each other.

Example:
```lean
example {W X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    [MeasurableSpace W] (κ : Kernel X Y) (η : Kernel Y Z) (ξ : Kernel Z W)
    [IsFiniteKernel ξ] [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    ξ ∘ₖ (η ∘ₖ κ) = ξ ∘ₖ η ∘ₖ κ := by
  kernel_hom
  exact Category.assoc _ _ _
``` -/
syntax (name := kernelHom) "kernel_hom" (ppSpace location)? : tactic

elab_rules : tactic
  | `(tactic| kernel_hom $[$loc]?) =>
    HomEqualityAt <| expandOptLocation (Lean.mkOptionalNode loc)
