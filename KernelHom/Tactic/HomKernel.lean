/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import KernelHom.Tactic.KernelHom
public import EqLift.Tactic.Kernel.KernelUnlift
public meta import Qq

/-!
# `hom_kernel` tactic

This file implements the `hom_kernel` tactic, the inverse of `kernel_hom`.
It transforms equalities written in the monoidal category back into
equivalent equalities of kernels.

## Main declarations

* `homToKernel`: recursive translation from categorical morphism expressions to kernel expressions.
* `homToKernelQ`: its typed version, for given carriers.
* `KernelEquality`: core implementation of `hom_kernel` on an equality.
* `hom_kernel`: user-facing tactic (with location support).
-/

public meta section

open Lean Elab Tactic Meta Qq CategoryTheory Parser.Tactic ProbabilityTheory MonoidalCategory
open scoped ComonObj

/-- The carrier of an object of `SFinKer` (see `typeOfObj`). -/
def getTypeFromSFinKer (SX : Expr) : MetaM Expr := do
  typeOfObj (← objLevel SX) SX

/-- An object `SX` of `SFinKer.{u}` with its carrier `X`, the `MeasurableSpace` instance of `X` and
the measurable equivalence `SX ≃ᵐ X` of `homCarrier`. -/
def objCarrier (u : Level) (SX : Expr) : MetaM
    ((SX : Q(SFinKer.{u})) × (X : Q(Type u)) × (_ : Q(MeasurableSpace $X)) × Q($SX ≃ᵐ $X)) := do
  let ⟨X, mX, _, ex⟩ ← homCarrier u (← typeOfObj u SX)
  return ⟨SX, X, mX, ex⟩

/-- The measurable equivalence `X ≃ᵐ X₀` from a lifted measurable space `X : Type u` to the original
space `X₀` (see `getOriginalType` and `constructMeasurableEquiv`). -/
def originalEquiv (u : Level) (X : Q(Type u)) {mX : Q(MeasurableSpace $X)} :
    MetaM ((v : Level) × (X₀ : Q(Type v)) × (_ : Q(MeasurableSpace $X₀)) × Q($X ≃ᵐ $X₀)) := do
  let (X₀, v) ← getOriginalType X
  let (e₀, _) ← constructMeasurableEquiv X₀ v u
  have X₀ : Q(Type v) := X₀
  return ⟨v, X₀, ← synthInstanceQCached q(MeasurableSpace $X₀), e₀⟩

/-- Given a proof of `f = κ.toHom`, return `κ` with the proof. -/
def withKernelOfProof (pf : Expr) : MetaM (Expr × Expr) := do
  let some (_, _, hom) := (← inferType pf).eq? | throwError "Expected an equality, got: {pf}."
  let_expr Kernel.toHom _ _ _ _ _ _ _ _ κ _ := hom | throwError "Expected a hom expression: {hom}."
  return (κ, pf)

/-- Translation of the left or right unitor `(λ_ SX).hom`, `(ρ_ SX).hom` or of their inverses. -/
def unitorToKernel (u : Level) (SX : Expr) (left hom : Bool) : MetaM (Expr × Expr) := do
  let ⟨SX, X, _, ex⟩ ← objCarrier u SX
  let ⟨v, _, _, ex₀⟩ ← originalEquiv u X
  withKernelOfProof <| match left, hom with
    | true, true => q(Kernel.leftUnitor_hom.{u, u, v, 0} $SX $ex $ex₀)
    | true, false => q(Kernel.leftUnitor_inv.{u, u, v, 0} $SX $ex $ex₀)
    | false, true => q(Kernel.rightUnitor_hom.{u, u, v, 0} $SX $ex $ex₀)
    | false, false => q(Kernel.rightUnitor_inv.{u, u, v, 0} $SX $ex $ex₀)

/-- Translation of the associator `(α_ SX SY SZ).hom` or of its inverse. -/
def associatorToKernel (u : Level) (SX SY SZ : Expr) (hom : Bool) : MetaM (Expr × Expr) := do
  let ⟨SX, X, _, ex⟩ ← objCarrier u SX
  let ⟨SY, Y, _, ey⟩ ← objCarrier u SY
  let ⟨SZ, Z, _, ez⟩ ← objCarrier u SZ
  let ⟨_, _, _, ex₀⟩ ← originalEquiv u X
  let ⟨_, _, _, ey₀⟩ ← originalEquiv u Y
  let ⟨_, _, _, ez₀⟩ ← originalEquiv u Z
  withKernelOfProof <| if hom then
      q(Kernel.associator_hom $SX $SY $SZ $ex $ey $ez $ex₀ $ey₀ $ez₀)
    else q(Kernel.associator_inv $SX $SY $SZ $ex $ey $ez $ex₀ $ey₀ $ez₀)

mutual

/-- Recursive translation of a morphism `e` of `SFinKer.{u}` into a kernel `e'`. Returns `e'`
together with a proof of `e = e'.toHom`, where the carriers of the source and of the target of `e`
are given by `objCarrier`. Each step is a single application of a translation lemma, given the
translations of the subterms (`Kernel.comp_toHom_of_eq`, `Kernel.parallelComp_toHom_of_eq`, ...). -/
partial def homToKernel (u : Level) (e : Expr) : MetaM (Expr × Expr) := do
  match_expr e with
  | CategoryStruct.comp _ _ SX SY SZ f g =>
    let ⟨_, _, _, ex⟩ ← objCarrier u SX
    let ⟨_, _, _, ey⟩ ← objCarrier u SY
    let ⟨_, _, _, ez⟩ ← objCarrier u SZ
    let ⟨_, κ, _, pf⟩ ← homToKernelQ ex ey f
    let ⟨_, η, _, pg⟩ ← homToKernelQ ey ez g
    return (q($η ∘ₖ $κ), q(Kernel.comp_toHom_of_eq $pf $pg))
  | MonoidalCategoryStruct.tensorHom _ _ _ SX SY SZ ST f g =>
    let ⟨_, _, _, ex⟩ ← objCarrier u SX
    let ⟨_, _, _, ey⟩ ← objCarrier u SY
    let ⟨_, _, _, ez⟩ ← objCarrier u SZ
    let ⟨_, _, _, et⟩ ← objCarrier u ST
    let ⟨_, κ, _, pf⟩ ← homToKernelQ ex ey f
    let ⟨_, η, _, pg⟩ ← homToKernelQ ez et g
    return (q($κ ∥ₖ $η), q(Kernel.parallelComp_toHom_of_eq $pf $pg))
  | MonoidalCategoryStruct.whiskerLeft _ _ _ SZ SX SY f =>
    let ⟨SZ, Z, mZ, ez⟩ ← objCarrier u SZ
    let ⟨_, _, _, ex⟩ ← objCarrier u SX
    let ⟨_, _, _, ey⟩ ← objCarrier u SY
    let ⟨_, κ, _, pf⟩ ← homToKernelQ ex ey f
    return (q(@Kernel.id $Z $mZ ∥ₖ $κ), q(Kernel.whiskerLeft_of_eq $SZ $ez $pf))
  | MonoidalCategoryStruct.whiskerRight _ _ _ SX SY f SZ =>
    let ⟨_, _, _, ex⟩ ← objCarrier u SX
    let ⟨_, _, _, ey⟩ ← objCarrier u SY
    let ⟨SZ, Z, mZ, ez⟩ ← objCarrier u SZ
    let ⟨_, κ, _, pf⟩ ← homToKernelQ ex ey f
    return (q($κ ∥ₖ @Kernel.id $Z $mZ), q(Kernel.whiskerRight_of_eq $SZ $ez $pf))
  | CategoryStruct.id _ _ SX =>
    let ⟨SX, X, mX, ex⟩ ← objCarrier u SX
    return (q(@Kernel.id $X $mX), q(Kernel.id_toHom $SX $ex))
  | ComonObj.counit _ _ _ SX _ =>
    let ⟨SX, X, _, ex⟩ ← objCarrier u SX
    return (q(Kernel.discard.{u, u} $X), q(Kernel.counit.{u, u, u} $SX $ex))
  | ComonObj.comul _ _ _ SX _ =>
    let ⟨SX, X, _, ex⟩ ← objCarrier u SX
    return (q(Kernel.copy $X), q(Kernel.comul $SX $ex))
  | Kernel.toHom _ _ _ _ _ _ _ _ κ _ => return (κ, ← mkEqRefl e)
  | Iso.hom _ _ _ _ iso =>
    match_expr iso with
    | BraidedCategory.braiding _ _ _ _ SX SY =>
      let ⟨SX, X, _, ex⟩ ← objCarrier u SX
      let ⟨SY, Y, _, ey⟩ ← objCarrier u SY
      return (q(Kernel.swap $X $Y), q(Kernel.braiding_hom $SX $SY $ex $ey))
    | MonoidalCategoryStruct.leftUnitor _ _ _ SX => unitorToKernel u SX true true
    | MonoidalCategoryStruct.rightUnitor _ _ _ SX => unitorToKernel u SX false true
    | MonoidalCategoryStruct.associator _ _ _ SX SY SZ => associatorToKernel u SX SY SZ true
    | _ => throwError "Unexpected isomorphism {iso}."
  | Iso.inv _ _ _ _ iso =>
    match_expr iso with
    | MonoidalCategoryStruct.leftUnitor _ _ _ SX => unitorToKernel u SX true false
    | MonoidalCategoryStruct.rightUnitor _ _ _ SX => unitorToKernel u SX false false
    | MonoidalCategoryStruct.associator _ _ _ SX SY SZ => associatorToKernel u SX SY SZ false
    | _ => throwError "Unexpected isomorphism {iso}."
  | _ => throwError "Expected a hom expression, got: {e}."

/-- Typed version of `homToKernel`, for a morphism `f : SX ⟶ SY` and the carriers `ex : SX ≃ᵐ X`
and `ey : SY ≃ᵐ Y` given by `objCarrier` (as in `homToKernel`): returns `f`, its translation
`κ : Kernel X Y` with its `IsSFiniteKernel` instance and the proof of `f = κ.toHom`. -/
partial def homToKernelQ {u : Level} {X Y : Q(Type u)} {mX : Q(MeasurableSpace $X)}
    {mY : Q(MeasurableSpace $Y)} {SX SY : Q(SFinKer.{u})} (ex : Q($SX ≃ᵐ $X)) (ey : Q($SY ≃ᵐ $Y))
    (f : Expr) : MetaM ((f : Q($SX ⟶ $SY)) × (κ : Q(Kernel $X $Y)) × (_ : Q(IsSFiniteKernel $κ)) ×
      Q($f = Kernel.toHom (ex := $ex) (ey := $ey) $κ)) := do
  let (κ, pf) ← homToKernel u f
  have κ : Q(Kernel $X $Y) := κ
  return ⟨f, κ, ← synthInstanceQCached q(IsSFiniteKernel $κ), pf⟩

end

/-- Translation of a morphism of `SFinKer` into a kernel, see `homToKernel`. -/
def transformHomToKernel (e : Expr) : MetaM (Expr × Expr) := do
  let_expr Quiver.Hom _ _ SX _ := ← inferType e | throwError "Expected a morphism, got: {e}."
  homToKernel (← objLevel SX) e

/-- Transform a `SFinKer` equality into an equivalent equality of kernels, along with a proof of
equivalence. The products `×ₖ` and composition-products `⊗ₖ` are folded back (`foldKernelOp`). -/
def KernelEquality (eq : Expr) : MetaM (Expr × Expr) := do
  resetTransformCache
  let eq ← whnfR <| ← instantiateMVars eq
  let some (_, lhs, rhs) := eq.eq? | throwError "Expected an equality, got: {eq}."
  let_expr Quiver.Hom _ _ SX _ := ← inferType lhs | throwError "Expected a morphism, got: {lhs}."
  let u ← objLevel SX
  let (κ, pf) ← homToKernel u lhs
  let (η, pg) ← homToKernel u rhs
  let (unlifted_expr, unlifted_proof) ← unliftEquality (← mkEq κ η)
  let (folded_expr, folded_proof) ← foldKernelOp unlifted_expr
  let kernel_eq_proof ← mkEqSymm (← mkAppM ``Kernel.toHom_congr_of_eq #[pf, pg])
  return (folded_expr, ← mkEqTrans (← mkEqTrans kernel_eq_proof unlifted_proof) folded_proof)

/-- The `hom_kernel` tactic is the inverse of `kernel_hom`: it transforms an
equality written in the monoidal category back to an equivalent equality of
s-finite kernels.

The tactic supports location specifiers like `rw` or `simp`:
- `hom_kernel` — applies to the goal
- `hom_kernel at h` — applies to hypothesis `h`
- `hom_kernel at h₁ h₂` — applies to multiple hypotheses
- `hom_kernel at h ⊢` — applies to hypothesis `h` and the goal
- `hom_kernel at *` — applies to all hypotheses and the goal

It is useful to switch back to kernel equations once categorical rewrites are done. -/
syntax (name := homKernel) "hom_kernel" (ppSpace location)? : tactic

elab_rules : tactic
  | `(tactic| hom_kernel $[$loc]?) =>
    expandOptLocation (Lean.mkOptionalNode loc) |> applyLocTactic <| KernelEquality
