/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import KernelHom.Tactic.KernelHom
public import KernelLift.Tactic.KernelUnlift

/-!
# `hom_kernel` tactic

This file implements the `hom_kernel` tactic, the inverse of `kernel_hom`.
It transforms equalities written in the monoidal category back into
equivalent equalities of kernels.

## Main declarations

* `transformHomToKernel`: recursive translation from categorical morphism expressions to
  kernel expressions.
* `mkHomKernelEqProof`: construction of the equivalence proof used by the
  tactic.
* `applyHomKernel`: core implementation on goals and hypotheses.
* `hom_kernel`: user-facing tactic (with location support).
-/

public meta section

open Lean Elab Tactic Meta CategoryTheory Parser.Tactic ProbabilityTheory MonoidalCategory
open ProbabilityTheory.Kernel

/- /-- Get the original type and its universe from a `SFinKer.of` expression. -/
partial def getTypeFromSFinKer (e : Expr) : MetaM (Expr × Level) := do
  let ewhnf ← whnf e
  match ewhnf.getAppFn with
  | Expr.const ``PUnit _ | Expr.const ``Unit _ =>
    return (Expr.const ``Unit [], Level.zero)
  | Expr.const ``Prod _ =>
    let args := ewhnf.getAppArgs
    let X := args[0]!
    let Y := args[1]!
    let (ex, xLvl) ← getTypeFromSFinKer X
    let (ey, yLvl) ← getTypeFromSFinKer Y
    let res ← mkAppOptM' (Expr.const ``Prod [xLvl, yLvl]) #[ex, ey]
    return (res, Level.max xLvl yLvl)
  | Expr.const ``ULift _ =>
    let args := ewhnf.getAppArgs
    let X := args[0]!
    return ← getTypeFromSFinKer X
  | Expr.const ``tensorUnit _ =>
    return (Expr.const ``Unit [], Level.zero)
  | Expr.const ``SFinKer.of _ =>
    let args := ewhnf.getAppArgs
    if args.size < 1 then
      throwError "SFinKer.of with insufficient arguments: {e}"
    else
      return ← getTypeFromSFinKer args[0]!
  | _ =>
    match ← getLevel e with
    | Level.succ l => return (e, l)
    | _ => throwError "Expected a type with a universe level ≥ 0, got: {e}" -/

/-- Get the original type and its universe from a `SFinKer.of` expression. -/
partial def getTypeFromSFinKer (e : Expr) : MetaM Expr := do
  match e.getAppFn with
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
  | _ => throwError "Expected a SFinKer.of expression, got: {e}"

/-- Deconstruct a left or right whisker to get the underlying kernel and the whiskered object -/
def deconstructWhiskersHomArgs (e : Expr) (eLvl : Level) (left : Bool) :
    MetaM (Expr × Expr × CategoryOP) := do
  let args := e.getAppArgs
  let SX := if left then args[args.size - 4]! else args[args.size - 1]!
  let κ := if left then args[args.size - 1]! else args[args.size - 2]!
  let X ← getTypeFromSFinKer SX
  let mXUnit ← synthInstance (mkApp (Expr.const ``MeasurableSpace [eLvl]) X)
  let kernel_id ← mkAppOptM ``Kernel.id #[X, mXUnit]
  let OP ← if left then pure <| .WhiskerLeft (← idME X) SX else pure <| .WhiskerRight (← idME X) SX
  return (κ, kernel_id, OP)

def getKernelRHSEqProofType (e : Expr) : MetaM Expr := do
  let some (_, _, hom_expr) := (← inferType e).eq? | throwError "Expected an equality, got: {e}"
  match hom_expr.getAppFn with
  | Expr.const ``Kernel.hom _ =>
    let args := hom_expr.getAppArgs
    return args[args.size - 2]!
  | _ => throwError "Expected a hom expression, got: {hom_expr}"

def deconstructUnitorsHom (e : Expr) (eLvl : Level) (left : Bool) :
    MetaM (Expr × CategoryOP) := do
  let args := e.getAppArgs
  let SX := args[args.size - 1]!
  let X ← getTypeFromSFinKer SX
  let ex ← idME X
  let (X₀, x₀Lvl) ← getOriginalType X
  let ex₀ ← constructMeasurableEquiv X₀ x₀Lvl eLvl
  let const :=
    if left then Expr.const ``Kernel.leftUnitor_hom [eLvl, x₀Lvl, eLvl, Level.zero]
    else Expr.const ``Kernel.rightUnitor_hom [eLvl, x₀Lvl, eLvl, Level.zero]
  let unitor_proof_eq ← mkAppOptM' const #[none, none, SX, ex, none, none, ex₀]
  let OPUnitor := if left then .LeftUnitor ex SX ex₀ else .RightUnitor ex SX ex₀
  return (← getKernelRHSEqProofType unitor_proof_eq, OPUnitor)

partial def transformHomToKernel (e : Expr) (op_data : List CategoryOP) :
    MetaM (Expr × List CategoryOP) := do
  match e.getAppFn with
  | Expr.const ``tensorHom _ =>
    let args := e.getAppArgs
    let κ := args[args.size - 2]!
    let η := args[args.size - 1]!
    let ST := args[args.size - 3]!
    let SZ := args[args.size - 4]!
    let SY := args[args.size - 5]!
    let SX := args[args.size - 6]!
    let (κ', lκ) ← transformHomToKernel κ op_data
    let (η', lη) ← transformHomToKernel η lκ
    let (X, Y, _, _) ← getTypesFromKernel κ'
    let (Z, T, _, _) ← getTypesFromKernel η'
    let OPParallelComp :=
        .ParallelComp (← idME X) SX (← idME Y) SY (← idME Z) SZ (← idME T) ST
    return (← mkAppM ``Kernel.parallelComp #[κ', η'], OPParallelComp :: lη)
  | Expr.const ``CategoryStruct.comp _ =>
    let args := e.getAppArgs
    let κ := args[args.size - 2]!
    let η := args[args.size - 1]!
    let SY := args[args.size - 3]!
    let SX := args[args.size - 4]!
    let SZ := args[args.size - 5]!
    let (κ', lκ) ← transformHomToKernel κ op_data
    let (η', lη) ← transformHomToKernel η lκ
    let (X, Y, _, _) ← getTypesFromKernel η'
    let (Z, _, _, _) ← getTypesFromKernel κ'
    let OPComp := .Comp (← idME X) SX (← idME Y) SY (← idME Z) SZ
    return (← mkAppM ``Kernel.comp #[η', κ'], OPComp :: lη)
  | Expr.const ``CategoryStruct.id [xLvl, _] =>
    let args := e.getAppArgs
    let SX := args[args.size - 1]!
    let X ← getTypeFromSFinKer SX
    let mX' ← synthInstance (mkApp (Expr.const ``MeasurableSpace [xLvl]) X)
    let id ← mkAppOptM ``Kernel.id #[X, mX']
    let OPId := .Id (← idME X) SX
    return (id, OPId :: op_data)
  | Expr.const ``ComonObj.counit [xLvl, _] =>
    let args := e.getAppArgs
    let SX := args[args.size - 2]!
    let X ← getTypeFromSFinKer SX
    let discard_kernel_const := Expr.const ``Kernel.discard [xLvl, xLvl]
    let OPDiscard := .Discard (← idME X) SX
    return (← mkAppOptM' discard_kernel_const #[X, none], OPDiscard :: op_data)
  | Expr.const ``ComonObj.comul [xLvl, _] =>
    let args := e.getAppArgs
    let SX := args[args.size - 2]!
    let X ← getTypeFromSFinKer SX
    let copy_kernel_const := Expr.const ``Kernel.copy [xLvl]
    let OPCopy := .Copy (← idME X) SX
    return (← mkAppOptM' copy_kernel_const #[X, none], OPCopy :: op_data)
  | Expr.const ``Kernel.hom _ =>
    let args := e.getAppArgs
    let κ := args[args.size - 2]!
    return (κ, op_data)
  | Expr.const ``MonoidalCategory.whiskerLeft [eLvl, _] =>
    let (κ, kernel_id, whiskerLeftOP) ← deconstructWhiskersHomArgs e eLvl true
    let (κ', lκ) ← transformHomToKernel κ op_data
    return (← mkAppM ``Kernel.parallelComp #[kernel_id, κ'], whiskerLeftOP :: lκ)
  | Expr.const ``MonoidalCategory.whiskerRight [eLvl, _] =>
    let (κ, kernel_id, whiskerRightOP) ← deconstructWhiskersHomArgs e eLvl false
    let (κ', lκ) ← transformHomToKernel κ op_data
    return (← mkAppM ``Kernel.parallelComp #[κ', kernel_id], whiskerRightOP :: lκ)
  | Expr.const ``Iso.hom _ =>
    let args := e.getAppArgs
    let iso := args[args.size - 1]!
    match iso.getAppFn with
    | Expr.const ``BraidedCategory.braiding _ =>
      let iso_args := iso.getAppArgs
      let SY := iso_args[iso_args.size - 1]!
      let SX := iso_args[iso_args.size - 2]!
      let Y ← getTypeFromSFinKer SY
      let X ← getTypeFromSFinKer SX
      let OPBraiding := .BraidingHom (← idME X) SX (← idME Y) SY
      return (← mkAppOptM ``Kernel.swap #[X, Y, none, none], OPBraiding :: op_data)
    | Expr.const ``leftUnitor [eLvl, _] =>
      let (left_unitor_expr, OPLeftUnitor) ← deconstructUnitorsHom iso eLvl true
      return (left_unitor_expr, OPLeftUnitor :: op_data)
    | Expr.const ``rightUnitor [eLvl, _] =>
      let (right_unitor_expr, OPRightUnitor) ← deconstructUnitorsHom iso eLvl false
      return (right_unitor_expr, OPRightUnitor :: op_data)
    | Expr.const ``MonoidalCategory.associator [eLvl, _] =>
      sorry
    | _ => throwError "Unexpected isomorphism {iso}"
  | _ => throwError "Expected a hom expression, got: {e}"

/-- Get the universe level from the left side of an equality expression. -/
def getUniverseFromEq (eq : Expr) : MetaM Level := do
  let eq ← instantiateMVars eq
  let eq ← zetaReduce eq
  let eq ← whnf eq
  let eq := eq.consumeMData
  let some (_, lhs, _) := eq.eq? | throwError "Expected an equality, got: {eq}"
  let l ← getLevel (← inferType lhs)
  match l with
  | Level.succ l' => return l'
  | _ => throwError "Expected a universe level ≥ 1, got: {l}"

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
def ApplyHomKernel (goal : MVarId) (fvarId : Option FVarId) : TacticM MVarId := do
  goal.withContext do
    let expr ← match fvarId with
        | some fid => do
          let decl ← fid.getDecl
          pure decl.type
        | none => goal.getType
    let expr ← whnfR <| ← instantiateMVars expr
    let (kernel_expr, op_data, _, _) ← transformEquality expr CategoryOP transformHomToKernel
    let (unlifted_expr, construct_unlifted_proof) ← do
      logInfo m!"Kernel expression: {kernel_expr}"
      let (unlifted_expr, op_data, eLvl) ← UnliftEquality kernel_expr
      logInfo m!"Unlifted expression: {unlifted_expr}"
      if kernel_expr == unlifted_expr then
        logInfo m!"Kernel expression and unlifted expression are the same, no proof needed."
        pure (unlifted_expr, fun e ↦ pure e)
      else
        let unlifted_proof_type ← mkEq kernel_expr unlifted_expr
        logInfo m!"Unlifted proof type: {unlifted_proof_type}"
        let unlifted_proof ← mkKernelUnliftEqProof unlifted_proof_type eLvl op_data
        pure (unlifted_expr, (fun e ↦ mkEqTrans e unlifted_proof))
    logInfo m!"Orignal expression: {expr}"
    logInfo m!"Kernel expression: {kernel_expr}"
    logInfo m!"Unlifed expression: {unlifted_expr}"

    let kernel_eq_proof_type ← mkEq expr kernel_expr
    logInfo m!"Equivalence proof type: {kernel_eq_proof_type}"
    let kernel_eq_proof ← mkKernelHomEqProof kernel_eq_proof_type op_data

    let eq_proof ← construct_unlifted_proof kernel_eq_proof
    logInfo m!"Equivalence proof: {eq_proof}"
    match fvarId with
    | some fid => do
      let mvarId ← getMainGoal
      let h_proof ← mkEqMP eq_proof (mkFVar fid)
      let userName := (← fid.getDecl).userName
      let mvarId ← mvarId.assert userName unlifted_expr h_proof
      let mvarId ← mvarId.tryClear fid
      let (_, mvarId) ← mvarId.intro1P
      pure mvarId
    | none => do
      let mvarId ← getMainGoal
      mvarId.replaceTargetEq unlifted_expr eq_proof

@[inherit_doc ApplyHomKernel]
syntax (name := homKernel) "hom_kernel" (ppSpace location)? : tactic

elab_rules : tactic
  | `(tactic| hom_kernel $[$loc]?) =>
    expandOptLocation (Lean.mkOptionalNode loc) |> applyLocTactic <| ApplyHomKernel

variable {X Y Z T : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  [MeasurableSpace T]

variable (κ : Kernel X Y) [IsSFiniteKernel κ] (η : Kernel Y Z) [IsSFiniteKernel η]

/- example : κ = (0 : Kernel X Y) := by
  kernel_hom
  hom_kernel
  sorry -/

example : Kernel.id (α := X × Y) = (0 : Kernel (X × Y) (X × Y)) := by
  kernel_hom
  hom_kernel
  sorry

example : Kernel.discard X = (0 : Kernel X Unit) := by
  kernel_hom
  hom_kernel
  sorry

example : Kernel.copy (X × Y) = (0 : Kernel (X × Y) ((X × Y) × (X × Y))) := by
  kernel_hom
  hom_kernel
  sorry

example : Kernel.swap (X × Y) (Z × T) = (0) := by
  kernel_hom
  hom_kernel
  sorry

example : (Kernel.id (α := (Z × T)) ∥ₖ κ) = (0 : Kernel ((Z × T) × X) ((Z × T) × Y)) := by
  kernel_hom
  hom_kernel
  sorry

example : (κ ∥ₖ Kernel.id (α := (Z × T))) = (0 : Kernel (X × (Z × T)) (Y × (Z × T))) := by
  kernel_hom
  hom_kernel
  sorry

example : κ ∥ₖ η = 0 := by
  kernel_hom
  hom_kernel
  sorry

example : Kernel.id.map (Prod.snd : Unit × X → X) = (0 : Kernel (Unit × X) X) := by
  kernel_hom
  hom_kernel
  sorry

example : Kernel.id.map (Prod.fst : X × Unit → X) = (0 : Kernel (X × Unit) X) := by
  kernel_hom
  hom_kernel
  sorry
