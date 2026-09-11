/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import KernelHom.Tactic.KernelHom
public import EqLift.Tactic.Kernel.KernelUnlift

/-!
# `hom_kernel` tactic

This file implements the `hom_kernel` tactic, the inverse of `kernel_hom`.
It transforms equalities written in the monoidal category back into
equivalent equalities of kernels.

## Main declarations

* `transformHomToKernel`: recursive translation from categorical morphism expressions to
  kernel expressions.
* `KernelEquality`: core implementation of `hom_kernel` on an equality.
* `hom_kernel`: user-facing tactic (with location support).
-/

public meta section

open Lean Elab Tactic Meta CategoryTheory Parser.Tactic ProbabilityTheory MonoidalCategory
open ProbabilityTheory.Kernel

/-- Get the original type and its universe from a `SFinKer.of` expression. -/
partial def getTypeFromSFinKer (e : Expr) : MetaM Expr := do
  match e.getAppFn with
  | Expr.const ``tensorUnit [eLvl, _] =>
    return mkConst ``PUnit [eLvl.succ]
  | Expr.const ``SFinKer.of _ =>
    let args := e.getAppArgs
    return args[0]!
  | Expr.const ``MonoidalCategory.tensorObj _ =>
    let args := e.getAppArgs
    let SY := args[args.size - 1]!
    let SX := args[args.size - 2]!
    let Y ← getTypeFromSFinKer SY
    let X ← getTypeFromSFinKer SX
    mkAppOptM ``Prod #[X, Y]
  | _ => throwError "Expected a SFinKer.of expression, got: {e}."

/-- Given an equality between a categorical morphism (left) and a "morphized" kernel (right), get
the kernel on the right side of the equality. -/
def getKernelRHSEqProofType (e : Expr) : MetaM Expr := do
  let some (_, _, hom_expr) := (← inferType e).eq? | throwError "Expected an equality, got: {e}."
  match hom_expr.getAppFn with
  | Expr.const ``Kernel.hom _ =>
    let args := hom_expr.getAppArgs
    return args[args.size - 2]!
  | _ => throwError "Expected a hom expression, got: {hom_expr}."

/-- Deconstruct a left or right unitor [inverse] morphism. -/
def deconstructUnitors (e : Expr) (eLvl : Level) (left hom : Bool) :
    MetaM (Expr × Expr) := do
  let args := e.getAppArgs
  let SX := args[args.size - 1]!
  let X ← getTypeFromSFinKer SX
  let ex ← idME X eLvl
  let (X₀, x₀Lvl) ← getOriginalType X
  let (ex₀, _) ← constructMeasurableEquiv X₀ x₀Lvl eLvl
  let const_args := [eLvl, eLvl, x₀Lvl, Level.zero]
  let const_name :=
    if left then
      if hom then ``leftUnitor_hom
      else ``leftUnitor_inv
    else
      if hom then ``rightUnitor_hom
      else ``rightUnitor_inv
  let const := mkConst const_name const_args
  let unitor_proof_eq ← mkAppM' const #[SX, ex, ex₀]
  return (← getKernelRHSEqProofType unitor_proof_eq, unitor_proof_eq)

/-- Deconstruct an associator [inverse] morphism. -/
def deconstructAssociator (e : Expr) (eLvl : Level) (hom : Bool) : MetaM (Expr × Expr) := do
  let args := e.getAppArgs
  let SZ := args[args.size - 1]!
  let SY := args[args.size - 2]!
  let SX := args[args.size - 3]!
  let Z ← getTypeFromSFinKer SZ
  let Y ← getTypeFromSFinKer SY
  let X ← getTypeFromSFinKer SX
  let (Z₀, z₀Lvl) ← getOriginalType Z
  let (Y₀, y₀Lvl) ← getOriginalType Y
  let (X₀, x₀Lvl) ← getOriginalType X
  let (ez₀, _) ← constructMeasurableEquiv Z₀ z₀Lvl eLvl
  let (ey₀, _) ← constructMeasurableEquiv Y₀ y₀Lvl eLvl
  let (ex₀, _) ← constructMeasurableEquiv X₀ x₀Lvl eLvl
  let associator_const := mkConst
    (if hom then ``Kernel.associator_hom else ``Kernel.associator_inv)
    [eLvl, eLvl, eLvl, eLvl, x₀Lvl, y₀Lvl, z₀Lvl]
  let associator_proof_eq ← mkAppM' associator_const
    #[SX, SY, SZ, ← idME X eLvl, ← idME Y eLvl, ← idME Z eLvl, ex₀, ey₀, ez₀]
  return (← getKernelRHSEqProofType associator_proof_eq, associator_proof_eq)

/-- The `HomCarrier` of the carrier of an object of `SFinKer` living in universe `u`. -/
def homCarrierOfObj (SX : Expr) (u : Level) : MetaM HomCarrier := do
  HomCarrier.mk' ⟨← getTypeFromSFinKer SX, u⟩

/-- Recursive transformation from morphism expression in `SFinKer` to kernel expression.
Returns the kernel expression `e'` together with a proof of `e = e'.hom`, built by congruence from
the translation lemmas (`comp_hom`, `parallelComp_hom`, ...). -/
partial def transformHomToKernel (e : Expr) : MetaM (Expr × Expr) := do
  match e.getAppFn with
  | Expr.const ``tensorHom _ =>
    let args := e.getAppArgs
    let κ := args[args.size - 2]!
    let η := args[args.size - 1]!
    let (κ', pκ) ← transformHomToKernel κ
    let (η', pη) ← transformHomToKernel η
    let (X, Y) ← getCarriersFromKernel κ'
    let (Z, T) ← getCarriersFromKernel η'
    let (X, Y, Z, T) :=
      (← HomCarrier.mk' X, ← HomCarrier.mk' Y, ← HomCarrier.mk' Z, ← HomCarrier.mk' T)
    let pf := mkAppN (mkConst ``parallelComp_hom [X.lvl, Y.lvl, T.lvl, Z.lvl, X.lvl])
      (typeInstArgs #[X, Y, T, Z] ++ objEquivArgs #[X, Y, Z, T] ++
        #[κ', η', ← Z.sfinite T η', ← X.sfinite Y κ'])
    let h ← mkCongr (← mkCongrArg e.appFn!.appFn! pκ) pη
    let e' ← mkKernelParallelComp X Y Z T κ' η'
    return (e', ← mkEqTrans h pf)
  | Expr.const ``CategoryStruct.comp _ =>
    let args := e.getAppArgs
    let κ := args[args.size - 2]!
    let η := args[args.size - 1]!
    let (κ', pκ) ← transformHomToKernel κ
    let (η', pη) ← transformHomToKernel η
    let (X, Y) ← getCarriersFromKernel η'
    let (Z, _) ← getCarriersFromKernel κ'
    let (X, Y, Z) := (← HomCarrier.mk' X, ← HomCarrier.mk' Y, ← HomCarrier.mk' Z)
    let pf := mkAppN (mkConst ``comp_hom [X.lvl, Y.lvl, Z.lvl, X.lvl])
      (homLemmaArgs #[X, Y, Z] ++
        #[η', κ', ← X.sfinite Y η', ← Z.sfinite X κ'])
    let h ← mkCongr (← mkCongrArg e.appFn!.appFn! pκ) pη
    return (← mkKernelComp Z X Y η' κ', ← mkEqTrans h pf)
  | Expr.const ``CategoryStruct.id [u, _] =>
    let args := e.getAppArgs
    let X ← homCarrierOfObj args[args.size - 1]! u
    return (← mkKernelId X, mkAppN (mkConst ``id_hom [u, u]) (homLemmaArgs #[X]))
  | Expr.const ``ComonObj.counit [u, _] =>
    let args := e.getAppArgs
    let X ← homCarrierOfObj args[args.size - 2]! u
    return (← mkKernelDiscard X u,
      mkAppN (mkConst ``counit [u, u, u]) (homLemmaArgs #[X]))
  | Expr.const ``ComonObj.comul [u, _] =>
    let args := e.getAppArgs
    let X ← homCarrierOfObj args[args.size - 2]! u
    return (← mkKernelCopy X, mkAppN (mkConst ``comul [u, u]) (homLemmaArgs #[X]))
  | Expr.const ``Kernel.hom _ =>
    let args := e.getAppArgs
    return (args[args.size - 2]!, ← mkEqRefl e)
  | Expr.const ``MonoidalCategory.whiskerLeft [u, _] =>
    let args := e.getAppArgs
    let Z ← homCarrierOfObj args[args.size - 4]! u
    let X ← homCarrierOfObj args[args.size - 3]! u
    let Y ← homCarrierOfObj args[args.size - 2]! u
    let (κ', pκ) ← transformHomToKernel args[args.size - 1]!
    let pf := mkAppN (mkConst ``Kernel.whiskerLeft [u, u, u, u])
      (homLemmaArgs #[X, Y, Z] ++ #[κ', ← X.sfinite Y κ'])
    let h ← mkCongrArg e.appFn! pκ
    let e' ← mkKernelParallelComp Z Z X Y
      (← mkKernelId Z) κ'
    return (e', ← mkEqTrans h pf)
  | Expr.const ``MonoidalCategory.whiskerRight [u, _] =>
    let args := e.getAppArgs
    let X ← homCarrierOfObj args[args.size - 4]! u
    let Y ← homCarrierOfObj args[args.size - 3]! u
    let Z ← homCarrierOfObj args[args.size - 1]! u
    let (κ', pκ) ← transformHomToKernel args[args.size - 2]!
    let pf := mkAppN (mkConst ``Kernel.whiskerRight [u, u, u, u])
      (homLemmaArgs #[X, Y, Z] ++ #[κ', ← X.sfinite Y κ'])
    let h ← mkCongrFun (← mkCongrArg e.appFn!.appFn! pκ) Z.obj
    let e' ← mkKernelParallelComp X Y Z Z κ'
      (← mkKernelId Z)
    return (e', ← mkEqTrans h pf)
  | Expr.const ``Iso.hom _ =>
    let args := e.getAppArgs
    let iso := args[args.size - 1]!
    match iso.getAppFn with
    | Expr.const ``BraidedCategory.braiding [u, _] =>
      let args := iso.getAppArgs
      let X ← homCarrierOfObj args[args.size - 2]! u
      let Y ← homCarrierOfObj args[args.size - 1]! u
      return (← mkKernelSwap X Y,
        mkAppN (mkConst ``braiding_hom [u, u, u]) (homLemmaArgs #[X, Y]))
    | Expr.const ``leftUnitor [eLvl, _] => deconstructUnitors iso eLvl true true
    | Expr.const ``rightUnitor [eLvl, _] => deconstructUnitors iso eLvl false true
    | Expr.const ``MonoidalCategory.associator [eLvl, _] => deconstructAssociator iso eLvl true
    | _ => throwError "Unexpected isomorphism {iso}."
  | Expr.const ``Iso.inv _ =>
    let args := e.getAppArgs
    let iso := args[args.size - 1]!
    match iso.getAppFn with
    | Expr.const ``leftUnitor [eLvl, _] => deconstructUnitors iso eLvl true false
    | Expr.const ``rightUnitor [eLvl, _] => deconstructUnitors iso eLvl false false
    | Expr.const ``MonoidalCategory.associator [eLvl, _] => deconstructAssociator iso eLvl false
    | _ => throwError "Unexpected isomorphism {iso}."
  | _ => throwError "Expected a hom expression, got: {e}."

/-- Transform a `SFinKer` equality into an equivalent equality of kernels, along with a proof of
equivalence. -/
def KernelEquality (eq : Expr) : MetaM (Expr × Expr) := do
  resetTransformCache
  let eq ← whnfR <| ← instantiateMVars eq
  let some (_, lhs_hom, rhs_hom) := eq.eq? | throwError "Expected an equality, got: {eq}."
  let (lhs, pl) ← transformHomToKernel lhs_hom
  let (rhs, pr) ← transformHomToKernel rhs_hom
  let kernel_expr ← mkEq lhs rhs
  let (unlifted_expr, unlifted_proof) ← unliftEquality kernel_expr
  let kernel_eq_proof ← mkEqSymm (← mkHomCongrProof lhs rhs pl pr)
  return (unlifted_expr, ← mkEqTrans kernel_eq_proof unlifted_proof)

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
