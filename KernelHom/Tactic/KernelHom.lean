/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import KernelHom.Kernel.Hom
public import KernelHom.Tactic.Utils
public import KernelHom.ForMathlib.MeasurableEquiv
public import Lean.Elab.Tactic.Location
public import KernelLift.Tactic.KernelLift

/-!
# `kernel_hom` tactic

This file implements the `kernel_hom` tactic, which transforms equalities of
kernels into equivalent equalities in the monoidal category.

## Main declarations

* `transformKernelToHom`: recursive translation from kernel expressions to
  categorical morphism expressions.
* `mkKernelHomEqProof`: construction of the equivalence proof used by the
  tactic.
* `applyKernelHom`: core implementation of `kernel_hom` on goals and hypotheses.
* `kernel_hom`: user-facing tactic (with location support).
-/

public meta section

open Lean Elab Tactic Meta CategoryTheory Parser.Tactic ProbabilityTheory MonoidalCategory
open ProbabilityTheory.Kernel

/-- Recursively decompose a product type into `SFinKer` objects with monoidal tensor structure. -/
partial def decomposeProductToSFinker (X : Expr) (xLvl : Level) : MetaM Expr := do
  match X.getAppFn with
  | Expr.const ``Prod _ =>
    let args := X.getAppArgs
    let t1 ← decomposeProductToSFinker args[0]! xLvl
    let t2 ← decomposeProductToSFinker args[1]! xLvl
    mkAppM ``tensorObj #[t1, t2]
  | _ =>
    mkAppOptM ``SFinKer.of #[X, none]

/-- Compute the `SFinKer` object corresponding to a measurable space. -/
def computeSFinkerOf (X : Expr) (xLvl : Level) : MetaM Expr := do
  match X with
  | Expr.const ``PUnit _ | Expr.const ``Unit _ =>
    let tensorunit :=
      Expr.const ``tensorUnit [xLvl, xLvl.succ]
    let sfinker := Expr.const ``SFinKer [xLvl]
    mkAppOptM' tensorunit #[sfinker, none, none]
  | _ =>
    decomposeProductToSFinker X xLvl

partial def idME (X : Expr) : MetaM Expr := do
  match X.getAppFn with
  | Expr.const ``Prod _ =>
    let args := X.getAppArgs
    let id1 ← idME args[0]!
    let id2 ← idME args[1]!
    mkAppM ``MeasurableEquiv.prod #[id1, id2]
  | Expr.const ``PUnit [xLvl] | Expr.const ``Unit [xLvl] =>
    let xLvl ← match xLvl with
      | Level.succ l => pure l
      | _ => throwError "Expected a successor level for PUnit/Unit, got: {xLvl}"
    let punitME := Expr.const ``MeasurableEquiv.punit [xLvl, xLvl]
    mkAppM' punitME #[]
  | _ =>
    mkAppOptM ``MeasurableEquiv.id #[X, none]

/-- Check if a kernel expression corresponds to a left or right whisker. -/
def checkWhiskers (κ : Expr) (offset : Nat) : MetaM Bool := do
  let κ := κ.consumeMData
  let args := κ.getAppArgs
  let idKernel := args[args.size - offset]!
  if !idKernel.getAppFn.isConstOf ``Kernel.id then
    return false
  else return true

/-- Check if a kernel expression corresponds to a left whisker. -/
def checkWhiskerLeft (κ : Expr) : MetaM Bool := checkWhiskers κ 2

/-- Check if a kernel expression corresponds to a right whisker. -/
def checkWhiskerRight (κ : Expr) : MetaM Bool := checkWhiskers κ 1

/-- Construct the relevant data for converting a kernel expression to its whisker morphism
representation. -/
def constructWhiskersArgs (e X : Expr) (left : Bool) :
    MetaM (Expr × Expr × Expr) := do
  let (Z, zLvl) ← match X.getAppFn with
  | Expr.const ``Prod univs =>
    let args := X.getAppArgs
    pure (args[left.toNat]!, univs[left.toNat]!)
  | _ =>
    if left then throwError "Expected left whisker with source Z × X, got: {X}"
    else throwError "Expected right whisker with source X × Z, got: {X}"
  let sfinkerOfZ ← computeSFinkerOf Z zLvl
  let κ ← match e.getAppFn with
    | Expr.const ``Kernel.parallelComp _ =>
      let args := e.getAppArgs
      pure args[args.size - (left.toNat + 1)]!
    | _ =>
      if left then throwError "Expected left whisker with parallelComp, got: {e}"
      else throwError "Expected right whisker with parallelComp, got: {e}"
  return (sfinkerOfZ, κ, Z)

/-- Check if a kernel expression corresponds to a left or right unitor. -/
def checkUnitors (κ : Expr) (offset : Nat) (prod : Name) : MetaM Bool := do
  let κ := κ.consumeMData
  if !κ.getAppFn.isConstOf ``Kernel.map then
    return false
  let args := κ.getAppArgs
  let fn := args[args.size - 1]!
  let idKernel := args[args.size - 2]!
  if !fn.getAppFn.isConstOf prod then
    return false
  if !idKernel.getAppFn.isConstOf ``Kernel.id then
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
def constructUnitors (X ex₀ : Expr) (xLvl : Level) (offset : Nat) :
    MetaM (Expr × CategoryOP) := do
  let left ← if offset == 0 then pure true
    else if offset == 1 then pure false
    else throwError "Invalid offset for unitors"
  let SX ← computeSFinkerOf X xLvl
  let unitor ← if left then mkAppM ``leftUnitor #[SX]
    else mkAppM ``rightUnitor #[SX]
  let unitorOP ← if left then pure <| .LeftUnitor (← idME X) SX ex₀
    else pure <|.RightUnitor (← idME X) SX ex₀
  return (← mkAppM ``Iso.hom #[unitor], unitorOP)

/-- Check if a kernel expression corresponds to an associator morphism or its inverse. -/
def checkAssociator (κ : Expr) (hom : Bool) : MetaM Bool := do
  let κ := κ.consumeMData
  if !κ.getAppFn.isConstOf ``Kernel.deterministic then
    return false
  let args := κ.getAppArgs
  let fn := args[args.size - 2]!
  if !fn.getAppFn.isConstOf ``DFunLike.coe then
    return false
  let fn := fn.getAppArgs[fn.getAppApps.size - 1]!
  if hom then
    if !fn.getAppFn.isConstOf ``MeasurableEquiv.prodAssoc then
      return false
  else
    if !fn.getAppFn.isConstOf ``MeasurableEquiv.symm then
      return false
    let innerFn := fn.getAppArgs[fn.getAppArgs.size - 1]!
    if !innerFn.getAppFn.isConstOf ``MeasurableEquiv.prodAssoc then
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
    | _ => throwError "Expected a product of two types, got: {prod.getAppArgs[1]!}"
  | _ => throwError "Expected a product of three types, got: {prod}"

def getMEFromThreeProds (me_prod : Expr) :
    MetaM (Expr × Expr × Expr) := do
  match me_prod.getAppFn with
  | Expr.const ``MeasurableEquiv.prod _ =>
    let args := me_prod.getAppArgs
    let ex := args[args.size - 2]!
    let right := args[args.size - 1]!
    match right.getAppFn with
    | Expr.const ``MeasurableEquiv.prod _ =>
      let rightArgs := right.getAppArgs
      let ey := rightArgs[rightArgs.size - 2]!
      let ez := rightArgs[rightArgs.size - 1]!
      return (ex, ey, ez)
    | _ => throwError "Expected a product of two measurable equivalences, got: {right}"
  | _ => throwError "Expected a product of three measurable equivalences, got: {me_prod}"

/-- Construct the associator morphism or its inverse. -/
def constructAssociator (left right ex₀ ey₀ ez₀ : Expr) (hom : Bool) :
    MetaM (Expr × CategoryOP) := do
  let (X, Y, Z, xLvl, yLvl, zLvl) ← if hom then getTypesFromThreeProds right
    else getTypesFromThreeProds left
  let SX ← computeSFinkerOf X xLvl
  let SY ← computeSFinkerOf Y yLvl
  let SZ ← computeSFinkerOf Z zLvl
  let associator ← mkAppM ``MonoidalCategory.associator #[SX, SY, SZ]
  let associatorOP : CategoryOP ← if hom then
      pure <| .AssociatorHom SX (← idME X) SY (← idME Y) SZ (← idME Z) ex₀ ey₀ ez₀
    else
      pure <| .AssociatorInv SX (← idME X) SY (← idME Y) SZ (← idME Z) ex₀ ey₀ ez₀
  return (← mkAppM (if hom then ``Iso.hom else ``Iso.inv) #[associator], associatorOP)

/-- Construct the associator morphism. -/
def constructAssociatorHom (left right ex₀ ey₀ ez₀ : Expr) :=
  constructAssociator left right ex₀ ey₀ ez₀ true

/-- Construct the inverse associator morphism. -/
def constructAssociatorInv (left right ex₀ ey₀ ez₀ : Expr) :=
  constructAssociator left right ex₀ ey₀ ez₀ false

/-- Recursive transformation from kernel expressions to morphism expressions in the `SFinKer`
category. -/
partial def transformKernelToHom (e : Expr) (op_data : List CategoryOP) :
    MetaM (Expr × List CategoryOP) := do
  match e.getAppFn with
  | Expr.const ``Kernel.comp _ =>
    let args := e.getAppArgs
    let η := args[args.size - 2]!
    let κ := args[args.size - 1]!
    let (X, Y, xLvl, yLvl) ← getTypesFromKernel η
    let (Z, _, tLvl, _) ← getTypesFromKernel κ
    let SX ← computeSFinkerOf X xLvl
    let SY ← computeSFinkerOf Y yLvl
    let SZ ← computeSFinkerOf Z tLvl
    let OPComp := .Comp (← idME X) SX (← idME Y) SY (← idME Z) SZ
    let (κ', lκ') ← transformKernelToHom κ op_data
    let (η', lη') ← transformKernelToHom η lκ'
    return (← mkAppM ``CategoryStruct.comp #[κ', η'], OPComp :: lη')
  | Expr.const ``Kernel.parallelComp _ =>
    if ← checkWhiskerLeft e then
      let (X, _, _, _) ← getTypesFromKernel e
      let (SZ, κ, Z) ← constructWhiskersArgs e X false
      let (κ', lκ) ← transformKernelToHom κ op_data
      let whiskerleft ← mkAppM ``MonoidalCategory.whiskerLeft #[SZ, κ']
      let leftWhiskerOP := .WhiskerLeft (← idME Z) SZ
      return (whiskerleft, leftWhiskerOP :: lκ)
    else if ← checkWhiskerRight e then
      let (X, _, _, _) ← getTypesFromKernel e
      let (SZ, κ, Z) ← constructWhiskersArgs e X true
      let (κ', lκ) ← transformKernelToHom κ op_data
      let whiskerright ← mkAppM ``MonoidalCategory.whiskerRight #[κ', SZ]
      let rightWhiskerOP := .WhiskerRight (← idME Z) SZ
      return (whiskerright, rightWhiskerOP :: lκ)
    else
      let args := e.getAppArgs
      let κ := args[args.size - 2]!
      let η := args[args.size - 1]!
      let (X, Y, xLvl, yLvl) ← getTypesFromKernel κ
      let (Z, T, zLvl, tLvl) ← getTypesFromKernel η
      let SX ← computeSFinkerOf X xLvl
      let SY ← computeSFinkerOf Y yLvl
      let SZ ← computeSFinkerOf Z zLvl
      let ST ← computeSFinkerOf T tLvl
      let OPParallelComp :=
        .ParallelComp (← idME X) SX (← idME Y) SY (← idME Z) SZ (← idME T) ST
      let (κ', lκ') ← transformKernelToHom κ op_data
      let (η', lη') ← transformKernelToHom η lκ'
      return (← mkAppM ``tensorHom #[κ', η'], OPParallelComp :: lη')
  | Expr.const ``Kernel.id [xLvl] =>
    let X := e.getAppArgs[0]!
    let SX ← computeSFinkerOf X xLvl
    let OPId := .Id (← idME X) SX
    return (← mkAppM ``CategoryStruct.id #[SX], OPId :: op_data)
  | Expr.const ``Kernel.discard [xLvl, _] =>
    let X := e.getAppArgs[0]!
    let SX ← computeSFinkerOf X xLvl
    let OPDiscard := .Discard (← idME X) SX
    return (← mkAppOptM ``ComonObj.counit #[none, none, none, SX, none],
      OPDiscard :: op_data)
  | Expr.const ``Kernel.copy [xLvl] =>
    let X := e.getAppArgs[0]!
    let SX ← computeSFinkerOf X xLvl
    let OPCopy := .Copy (← idME X) SX
    return (← mkAppOptM ``ComonObj.comul #[none, none, none, SX, none],
      OPCopy :: op_data)
  | Expr.const ``Kernel.swap [xLvl, yLvl] =>
    let X := e.getAppArgs[0]!
    let Y := e.getAppArgs[1]!
    let SX ← computeSFinkerOf X xLvl
    let SY ← computeSFinkerOf Y yLvl
    let braiding ← mkAppM ``Iso.hom #[← mkAppM ``BraidedCategory.braiding #[SX, SY]]
    return (braiding, .BraidingHom (← idME X) SX (← idME Y) SY :: op_data)
  | Expr.const ``Kernel.lift _ =>
    let (X, Y, xLvl, yLvl) ← getTypesFromKernel e
    let args := e.getAppArgs
    let κ := args[args.size - 1]!
    if ← checkLeftUnitor κ then
      let ey₀ := args[args.size - 2]!
      let (leftUnitorExpr, OPLeftUnitor) ← constructUnitors Y ey₀ yLvl 0
      return (leftUnitorExpr, OPLeftUnitor :: op_data)
    else if ← checkRightUnitor κ then
      let ey₀ := args[args.size - 2]!
      let (rightUnitorExpr, OPRightUnitor) ← constructUnitors Y ey₀ yLvl 1
      return (rightUnitorExpr, OPRightUnitor :: op_data)
    else if ← checkAssociatorHom κ then
      let (ex₀, ey₀, ez₀) ← getMEFromThreeProds args[args.size - 2]!
      let (associatorExpr, associatorOP) ← constructAssociatorHom X Y ex₀ ey₀ ez₀
      return (associatorExpr, associatorOP :: op_data)
    else if ← checkAssociatorInv κ then
      let (ex₀, ey₀, ez₀) ← getMEFromThreeProds args[args.size - 3]!
      let (associatorInvExpr, associatorInvOP) ← constructAssociatorInv X Y ex₀ ey₀ ez₀
      return (associatorInvExpr, associatorInvOP :: op_data)
    else
      let SX ← computeSFinkerOf X xLvl
      let SY ← computeSFinkerOf Y yLvl
      let homExpr ← mkAppOptM ``ProbabilityTheory.Kernel.hom
        #[X, Y, none, none, SX, SY, (← idME X), (← idME Y), e, none]
      pure (homExpr, op_data)
  | _ =>
    let (X, Y, xLvl, yLvl) ← getTypesFromKernel e
    let SX ← computeSFinkerOf X xLvl
    let SY ← computeSFinkerOf Y yLvl
    let homExpr ← mkAppOptM ``ProbabilityTheory.Kernel.hom
      #[X, Y, none, none, SX, SY, (← idME X), (← idME Y), e, none]
    pure (homExpr, op_data)

/-- Construct the proof of equivalence between the original equality and the transformed one. -/
def mkKernelHomEqProof (eqProofType : Expr) (op_data : List CategoryOP) : TacticM Expr := do
  let savedGoals ← getGoals
  let mvar ← mkFreshExprSyntheticOpaqueMVar eqProofType
  let mvarId := mvar.mvarId!
  setGoals [mvarId]
  let op_data := op_data.reverse
  evalTactic (← `(tactic| apply propext))
  for op in op_data do
    match op with
    | .Comp ex SX ey SY ez SZ =>
      let terms ← exprsToSyntax #[ex, SX, ey, SY, ez, SZ]
      evalTactic (← `(tactic| nth_rw 1 [
        comp_hom
        (ex := $(terms[0]!))
        (SX := $(terms[1]!))
        (ey := $(terms[2]!))
        (SY := $(terms[3]!))
        (ez := $(terms[4]!))
        (SZ := $(terms[05]!))
      ]))
    | .ParallelComp ex SX ey SY ez SZ et ST =>
      let terms ← exprsToSyntax #[ex, SX, ey, SY, ez, SZ, et, ST]
      evalTactic (← `(tactic| nth_rw 1 [
        parallelComp_hom
        (ex := $(terms[0]!))
        (SX := $(terms[1]!))
        (ey := $(terms[2]!))
        (SY := $(terms[3]!))
        (ez := $(terms[4]!))
        (SZ := $(terms[5]!))
        (et := $(terms[6]!))
        (ST := $(terms[7]!))
      ]))
    | .Id ex SX =>
      let terms ← exprsToSyntax #[ex, SX]
      evalTactic (← `(tactic| nth_rw 1 [
        id_hom
        (ex := $(terms[0]!))
        (SX := $(terms[1]!))
      ]))
    | .Discard ex SX =>
      let terms ← exprsToSyntax #[ex, SX]
      evalTactic (← `(tactic| nth_rw 1 [
        counit
        (ex := $(terms[0]!))
        (SX := $(terms[1]!))
      ]))
    | .Copy ex SX =>
      let terms ← exprsToSyntax #[ex, SX]
      evalTactic (← `(tactic| nth_rw 1 [
        comul
        (ex := $(terms[0]!))
        (SX := $(terms[1]!))
      ]))
    | .WhiskerLeft ex SX =>
      let terms ← exprsToSyntax #[ex, SX]
      evalTactic (← `(tactic| nth_rw 1 [
        whiskerLeft
        (ez := $(terms[0]!))
        (SZ := $(terms[1]!))
      ]))
    | .WhiskerRight ex SX =>
      let terms ← exprsToSyntax #[ex, SX]
      evalTactic (← `(tactic| nth_rw 1 [
        whiskerRight
        (ez := $(terms[0]!))
        (SZ := $(terms[1]!))
      ]))
    | .LeftUnitor ex SX ex₀ =>
      let terms ← exprsToSyntax #[ex, SX, ex₀]
      logInfo m!"TEst"
      evalTactic (← `(tactic| nth_rw 1 [
        leftUnitor_hom
        (ex := $(terms[0]!))
        (SX := $(terms[1]!))
        (ex₀ := $(terms[2]!))
      ]))
    | .RightUnitor ex SX ex₀ =>
      let terms ← exprsToSyntax #[ex, SX, ex₀]
      evalTactic (← `(tactic| nth_rw 1 [
        rightUnitor_hom
        (ex := $(terms[0]!))
        (SX := $(terms[1]!))
        (ex₀ := $(terms[2]!))
      ]))
    | .AssociatorHom SX ex SY ey SZ ez ex₀ ey₀ ez₀ =>
      let terms ← exprsToSyntax #[SX, ex, SY, ey, SZ, ez, ex₀, ey₀, ez₀]
      evalTactic (← `(tactic| nth_rw 1 [
        Kernel.associator_hom
        (SX := $(terms[0]!))
        (ex := $(terms[1]!))
        (SY := $(terms[2]!))
        (ey := $(terms[3]!))
        (SZ := $(terms[4]!))
        (ez := $(terms[5]!))
        (ex₀ := $(terms[6]!))
        (ey₀ := $(terms[7]!))
        (ez₀ := $(terms[8]!))
      ]))
    | .AssociatorInv SX ex SY ey SZ ez ex₀ ey₀ ez₀ =>
      let terms ← exprsToSyntax #[SX, ex, SY, ey, SZ, ez, ex₀, ey₀, ez₀]
      evalTactic (← `(tactic| nth_rw 1 [
        associator_inv
        (SX := $(terms[0]!))
        (ex := $(terms[1]!))
        (SY := $(terms[2]!))
        (ey := $(terms[3]!))
        (SZ := $(terms[4]!))
        (ez := $(terms[5]!))
        (ex₀ := $(terms[6]!))
        (ey₀ := $(terms[7]!))
        (ez₀ := $(terms[8]!))
      ]))
    | .BraidingHom ex SX ey SY =>
      let terms ← exprsToSyntax #[ex, SX, ey, SY]
      evalTactic (← `(tactic| nth_rw 1 [
        braiding_hom
        (ex := $(terms[0]!))
        (SX := $(terms[1]!))
        (ey := $(terms[2]!))
        (SY := $(terms[3]!))
      ]))
  evalTactic (← `(tactic| rw [hom_congr]))
  if !(← getGoals).isEmpty then
    setGoals savedGoals
    throwError "Failed to solve all goals while building kernel_hom equivalence proof"
  setGoals savedGoals
  instantiateMVars mvar

/-- The `kernel_hom` tactic transforms a kernel equality to an equivalent equality in
the category of measurable spaces and s-finite kernels.

The tactic supports location specifiers like `rw` or `simp`:
* `kernel_hom` — applies to the goal
* `kernel_hom at h` — applies to hypothesis `h`
* `kernel_hom at h₁ h₂` — applies to multiple hypotheses
* `kernel_hom at h ⊢` — applies to hypothesis `h` and the goal
* `kernel_hom at *` — applies to all hypotheses and the goal

Example:
```lean
example {W X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    [MeasurableSpace W] (κ : Kernel X Y) (η : Kernel Y Z) (ξ : Kernel Z W)
    [IsFiniteKernel ξ] [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    ξ ∘ₖ (η ∘ₖ κ) = ξ ∘ₖ η ∘ₖ κ := by
  kernel_hom
  exact Category.assoc _ _ _
``` -/
def ApplyKernelHom (goal : MVarId) (fvarId : Option FVarId) : TacticM MVarId := do
  goal.withContext do
    let expr ← match fvarId with
        | some fid => do
          let decl ← fid.getDecl
          pure decl.type
        | none => goal.getType
    let expr ← whnfR <| ← unfoldKernelOp <| ← instantiateMVars expr

    /- Decide wether we need to lift the kernel expression to a homogeneous universe level first.
    If this is necessary, we also need to construct the proof of equivalence between the original
    expression and the lifted one, which will be used later to construct the final equivalence
    proof. -/
    let (lifted_expr, construct_lifted_proof) ← do
      let result ← (LiftEquality expr).run
      match result with
      | Except.error .AlreadyHomogeneous =>
        pure (expr, (fun e ↦ pure e))
      | Except.ok (lifted_expr, kernel_op_data, maxLvl) =>
        let lifted_proof_type ← mkEq expr lifted_expr
        let lifted_eq_proof ← mkKernelLiftEqProof lifted_proof_type maxLvl kernel_op_data
        pure (lifted_expr, (fun e ↦ mkEqTrans lifted_eq_proof e))
    let (hom_expr, op_data, _, _) ← transformEquality lifted_expr CategoryOP transformKernelToHom
    let hom_eq_proof_type ← mkEq lifted_expr hom_expr
    let hom_eq_proof ← mkKernelHomEqProof hom_eq_proof_type op_data
    let eq_proof ← construct_lifted_proof hom_eq_proof
    match fvarId with
    | some fid => do
      let mvarId ← getMainGoal
      let h_proof ← mkEqMP eq_proof (mkFVar fid)
      let userName := (← fid.getDecl).userName
      let mvarId ← mvarId.assert userName hom_expr h_proof
      let mvarId ← mvarId.tryClear fid
      let (_, mvarId) ← mvarId.intro1P
      pure mvarId
    | none => do
      let mvarId ← getMainGoal
      mvarId.replaceTargetEq hom_expr eq_proof

@[inherit_doc ApplyKernelHom]
syntax (name := kernelHom) "kernel_hom" (ppSpace location)? : tactic

elab_rules : tactic
  | `(tactic| kernel_hom $[$loc]?) =>
    expandOptLocation (Lean.mkOptionalNode loc) |> applyLocTactic <| ApplyKernelHom

variable {X Y Z T : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  [MeasurableSpace T]

variable (κ : Kernel X Y) [IsSFiniteKernel κ] (η : Kernel Y Z) [IsSFiniteKernel η]

example : Kernel.id (α := (X × Y)) = (0 : Kernel (X × Y) (X × Y)) := by
  kernel_hom
  sorry

example : Kernel.discard (X × Y) = (0 : Kernel (X × Y) PUnit) := by
  kernel_hom
  sorry

example : Kernel.copy (X × Y) = (0) := by
  kernel_hom
  sorry

example : (Kernel.id (α := Z) ∥ₖ κ) = (0 : Kernel (Z × X) (Z × Y)) := by
  kernel_hom
  sorry

example : (κ ∥ₖ Kernel.id (α := Z)) = (0 : Kernel (X × Z) (Y × Z)) := by
  kernel_hom
  sorry

example : Kernel.id.map (Prod.snd : PUnit × X → X) = (0 : Kernel (PUnit × X) X) := by
  kernel_hom
  sorry

example : Kernel.id.map (Prod.fst : X × PUnit → X) = (0 : Kernel (X × PUnit) X) := by
  kernel_hom
  sorry

open MeasurableEquiv in
example : Kernel.deterministic prodAssoc (by fun_prop) =
    (0 : Kernel (((X × Z) × Y) × Z) ((X × Z) × Y × Z)) := by
  kernel_hom
  sorry

open MeasurableEquiv in
example : Kernel.deterministic prodAssoc.symm (by fun_prop) =
    (0 : Kernel ((X × Z) × Y × Z) (((X × Z) × Y) × Z)) := by
  kernel_hom
  sorry

example : Kernel.swap (X × Z) Y = 0 := by
  kernel_hom
  sorry
