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
public meta import Qq

/-!
# `kernel_hom` tactic

This file implements the `kernel_hom` tactic, which transforms equalities of
kernels into equivalent equalities in the monoidal category.

## Main declarations

* `kernelToHom`: recursive translation from kernel expressions to categorical morphism expressions.
* `kernelToHomQ`: its typed version, for given carriers.
* `HomEquality`: core implementation of `kernel_hom` on an equality.
* `kernel_hom`: user-facing tactic (with location support).
-/

public meta section

open Lean Elab Tactic Meta Qq CategoryTheory Parser.Tactic ProbabilityTheory MonoidalCategory
open scoped ComonObj

/-- Whether `X` is `PUnit` or `Unit`. -/
def isPUnit (X : Expr) : Bool := X.isAppOf ``PUnit || X.isConstOf ``Unit

/-- Whether `κ` is the left unitor `Kernel.id.map Prod.snd : Kernel (PUnit × X) X` (or the right
unitor `Kernel.id.map Prod.fst : Kernel (X × PUnit) X` if `left` is false), as in
`Kernel.leftUnitor_hom` and `Kernel.rightUnitor_hom`. -/
def isUnitor (κ : Expr) (left : Bool) : Bool :=
  match_expr κ.consumeMData with
  | Kernel.map P _ _ _ _ _ id f =>
    let_expr Prod A B := P | false
    id.isAppOf ``Kernel.id && f.isAppOf (if left then ``Prod.snd else ``Prod.fst) &&
      isPUnit (if left then A else B)
  | _ => false

/-- Whether `κ` is the associator `Kernel.deterministic prodAssoc` (or its inverse
`Kernel.deterministic prodAssoc.symm` if `inv`), as in `Kernel.associator_hom` and
`Kernel.associator_inv`. -/
def isAssociator (κ : Expr) (inv : Bool) : Bool :=
  match_expr κ.consumeMData with
  | Kernel.deterministic _ _ _ _ f _ =>
    let_expr DFunLike.coe _ _ _ _ e := f | false
    if inv then
      let_expr MeasurableEquiv.symm _ _ _ _ e := e | false
      e.isAppOf ``MeasurableEquiv.prodAssoc
    else e.isAppOf ``MeasurableEquiv.prodAssoc
  | _ => false

/-- The components `ex ey ez` of a measurable equivalence `ex.prodCongr (ey.prodCongr ez)`. -/
def prodCongr₃? (e : Expr) : Option (Expr × Expr × Expr) := do
  let_expr MeasurableEquiv.prodCongr _ _ _ _ _ _ _ _ ex e := e | none
  let_expr MeasurableEquiv.prodCongr _ _ _ _ _ _ _ _ ey ez := e | none
  return (ex, ey, ez)

/-- Translation of the lifted left unitor `Kernel.id.map Prod.snd : Kernel (PUnit × X₀) X₀` (or of
the right unitor if `left` is false), where `X₀` is the source of the unitor and `e₀ : X ≃ᵐ X₀` the
measurable equivalence of the lifting of its target. -/
def unitorToHom (u : Level) (X₀ e₀ : Expr) (left : Bool) : MetaM (Expr × Expr) := do
  let .const _ [l₁, l₂] := X₀.getAppFn | throwError "Expected a product, got: {X₀}."
  let w := if left then l₁ else l₂
  let ⟨_, _, SX, ex, v, _, _, ex₀⟩ ← homCarrierOfEquiv u e₀
  if left then return (q((λ_ $SX).hom), q(Kernel.leftUnitor_hom.{u, u, v, w} $SX $ex $ex₀))
  else return (q((ρ_ $SX).hom), q(Kernel.rightUnitor_hom.{u, u, v, w} $SX $ex $ex₀))

/-- Translation of the lifted associator `Kernel.deterministic prodAssoc` (or of its inverse if
`inv`), where `e₀ = ea₀.prodCongr (eb₀.prodCongr ec₀)` is the measurable equivalence of the lifting
of its target (of its source for the inverse). -/
def associatorToHom (u : Level) (e₀ : Expr) (inv : Bool) : MetaM (Expr × Expr) := do
  let some (ea₀, eb₀, ec₀) := prodCongr₃? e₀
    | throwError "Expected a product of three measurable equivalences, got: {e₀}."
  let ⟨_, _, SA, ea, _, _, _, ea₀⟩ ← homCarrierOfEquiv u ea₀
  let ⟨_, _, SB, eb, _, _, _, eb₀⟩ ← homCarrierOfEquiv u eb₀
  let ⟨_, _, SC, ec, _, _, _, ec₀⟩ ← homCarrierOfEquiv u ec₀
  if inv then
    return (q((α_ $SA $SB $SC).inv),
      q(Kernel.associator_inv $SA $SB $SC $ea $eb $ec $ea₀ $eb₀ $ec₀))
  else
    return (q((α_ $SA $SB $SC).hom),
      q(Kernel.associator_hom $SA $SB $SC $ea $eb $ec $ea₀ $eb₀ $ec₀))

mutual

/-- Recursive translation of a lifted kernel `e` into a morphism `e'` of `SFinKer.{u}`. Returns `e'`
together with a proof of `e' = e.toHom`, where the carriers of the source and of the target of `e`
are given by `homCarrier`. Each step is a single application of a translation lemma, given the
translations of the subterms (`Kernel.comp_toHom_of_eq`, `Kernel.parallelComp_toHom_of_eq`, ...). -/
partial def kernelToHom (u : Level) (e : Expr) : MetaM (Expr × Expr) := do
  match_expr e with
  | Kernel.comp X Y Z _ _ _ η κ =>
    let ⟨_, _, _, ex⟩ ← homCarrier u X
    let ⟨_, _, _, ey⟩ ← homCarrier u Y
    let ⟨_, _, _, ez⟩ ← homCarrier u Z
    let ⟨_, _, f, pf⟩ ← kernelToHomQ ex ey κ
    let ⟨_, _, g, pg⟩ ← kernelToHomQ ey ez η
    return (q($f ≫ $g), q(Kernel.comp_toHom_of_eq $pf $pg))
  | Kernel.parallelComp X Y Z T _ _ _ _ κ η =>
    let ⟨_, _, SX, ex⟩ ← homCarrier u X
    let ⟨_, _, _, ey⟩ ← homCarrier u Y
    let ⟨_, _, SZ, ez⟩ ← homCarrier u Z
    let ⟨_, _, _, et⟩ ← homCarrier u T
    if κ.isAppOf ``Kernel.id then
      let ⟨_, _, g, pg⟩ ← kernelToHomQ ez et η
      return (q($SX ◁ $g), q(Kernel.whiskerLeft_of_eq $SX $ex $pg))
    else if η.isAppOf ``Kernel.id then
      let ⟨_, _, f, pf⟩ ← kernelToHomQ ex ey κ
      return (q($f ▷ $SZ), q(Kernel.whiskerRight_of_eq $SZ $ez $pf))
    else
      let ⟨_, _, f, pf⟩ ← kernelToHomQ ex ey κ
      let ⟨_, _, g, pg⟩ ← kernelToHomQ ez et η
      return (q($f ⊗ₘ $g), q(Kernel.parallelComp_toHom_of_eq $pf $pg))
  | Kernel.id X _ =>
    let ⟨_, _, SX, ex⟩ ← homCarrier u X
    return (q(𝟙 $SX), q(Kernel.id_toHom $SX $ex))
  | Kernel.discard X _ =>
    let ⟨_, _, SX, ex⟩ ← homCarrier u X
    return (q(ε[$SX]), q(Kernel.counit.{u, u, u} $SX $ex))
  | Kernel.copy X _ =>
    let ⟨_, _, SX, ex⟩ ← homCarrier u X
    return (q(Δ[$SX]), q(Kernel.comul $SX $ex))
  | Kernel.swap X Y _ _ =>
    let ⟨_, _, SX, ex⟩ ← homCarrier u X
    let ⟨_, _, SY, ey⟩ ← homCarrier u Y
    return (q((β_ $SX $SY).hom), q(Kernel.braiding_hom $SX $SY $ex $ey))
  | Kernel.lift X₀ _ _ _ X _ Y _ ex₀ ey₀ κ =>
    if isUnitor κ (left := true) then unitorToHom u X₀ ey₀ (left := true)
    else if isUnitor κ (left := false) then unitorToHom u X₀ ey₀ (left := false)
    else if isAssociator κ (inv := false) then associatorToHom u ey₀ (inv := false)
    else if isAssociator κ (inv := true) then associatorToHom u ex₀ (inv := true)
    else
      let ⟨X, _, SX, ex⟩ ← homCarrier u X
      let ⟨Y, _, SY, ey⟩ ← homCarrier u Y
      have e : Q(Kernel $X $Y) := e
      let _ ← synthInstanceQCached q(IsSFiniteKernel $e)
      have f : Q($SX ⟶ $SY) := q(Kernel.toHom (ex := $ex) (ey := $ey) $e)
      return (f, q(Eq.refl $f))
  | _ => throwError "Expected a lifted kernel expression, got: {e}."

/-- Typed version of `kernelToHom`, for a kernel `κ : Kernel X Y` and the carriers `ex : SX ≃ᵐ X`
and `ey : SY ≃ᵐ Y` of `X` and `Y` given by `homCarrier` (as in `kernelToHom`): returns `κ` with its
`IsSFiniteKernel` instance, its translation `f : SX ⟶ SY` and the proof of `f = κ.toHom`. -/
partial def kernelToHomQ {u : Level} {X Y : Q(Type u)} {mX : Q(MeasurableSpace $X)}
    {mY : Q(MeasurableSpace $Y)} {SX SY : Q(SFinKer.{u})} (ex : Q($SX ≃ᵐ $X)) (ey : Q($SY ≃ᵐ $Y))
    (κ : Expr) : MetaM ((κ : Q(Kernel $X $Y)) × (_ : Q(IsSFiniteKernel $κ)) × (f : Q($SX ⟶ $SY)) ×
      Q($f = Kernel.toHom (ex := $ex) (ey := $ey) $κ)) := do
  have κ : Q(Kernel $X $Y) := κ
  let hκ ← synthInstanceQCached q(IsSFiniteKernel $κ)
  let (f, pf) ← kernelToHom u κ
  return ⟨κ, hκ, f, pf⟩

end

/-- Translation of a lifted kernel into a morphism of `SFinKer`, see `kernelToHom`. -/
def transformKernelToHom (e : Expr) : MetaM (Expr × Expr) := do
  kernelToHom (← kernelLevel e) e

/-- Transform a kernel equality into an equivalent equality in `SFinKer`, along with a proof of
equivalence. The equality is first lifted to a common universe level using `lift`. -/
def HomEqualityWith (lift : Expr → MetaM (Expr × Expr)) (eq : Expr) : MetaM (Expr × Expr) := do
  let (eq, unfold_proof) ← unfoldKernelOp eq
  let (lifted_expr, lifted_proof) ← lift eq
  let some (_, lhs, rhs) := lifted_expr.eq? | throwError "Expected an equality, got: {lifted_expr}."
  let u ← kernelLevel lhs
  let (f, pf) ← kernelToHom u lhs
  let (g, pg) ← kernelToHom u rhs
  let hom_eq_proof ← mkAppM ``Kernel.toHom_congr_of_eq #[pf, pg]
  return (← mkEq f g, ← mkEqTrans unfold_proof (← mkEqTrans lifted_proof hom_eq_proof))

/-- Transform a kernel equality into an equivalent equality in `SFinKer`, along with a proof of
equivalence. -/
def HomEquality : Expr → MetaM (Expr × Expr) := HomEqualityWith liftEquality

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
    liftEqualityAt (expandOptLocation <| mkOptionalNode loc) HomEqualityWith
