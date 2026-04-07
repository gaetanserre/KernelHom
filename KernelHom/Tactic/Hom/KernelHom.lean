/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Lean.Elab.Tactic.Location
import KernelHom.Kernel.MonoidalComp
import KernelHom.Mathlib.MeasurableEquiv
import KernelHom.Tactic.LocTactic
import KernelHom.Tactic.Hom.Universe
import KernelHom.Tactic.Hom.Utils

/-!
# `kernel_hom` tactic

This file implements the `kernel_hom` tactic, which transforms equalities of
kernels into equivalent equalities in the monoidal category.

## Main declarations

- `transformKernelToHom`: recursive translation from kernel expressions to
  categorical morphism expressions.
- `mkKernelHomEqProof`: construction of the equivalence proof used by the
  tactic.
- `applyKernelHom`: core implementation on goals and hypotheses.
- `kernel_hom`: user-facing tactic (with location support).
-/

open Lean Elab Tactic Meta CategoryTheory Parser.Tactic ProbabilityTheory MonoidalCategory

/-- Check if a kernel expression corresponds to a left or right unitor. -/
def check_unitors (κ : Expr) (offset : Nat) (prod : Name) : MetaM Bool := do
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
  let (src, _, _) ← get_types_from_kernel κ
  let srcWhnf ← whnf src
  match srcWhnf.getAppFn with
  | Expr.const ``Prod _ =>
    let args := srcWhnf.getAppArgs
    if args.size < 2 then
      return false
    let punit? := args[offset]!
    match punit?.getAppFn with
    | Expr.const ``PUnit _ | Expr.const ``Unit _ => return true
    | _ => return false
  | _ => return false

/-- Check if a kernel expression corresponds to a left unitor. -/
def check_leftUnitor (κ : Expr) : MetaM Bool := check_unitors κ 0 ``Prod.snd

/-- Check if a kernel expression corresponds to a right unitor. -/
def check_rightUnitor (κ : Expr) : MetaM Bool := check_unitors κ 1 ``Prod.fst

/-- Recursively decompose a product type into `SFinKer` objects with monoidal tensor structure. -/
partial def decomposeProductToSFinker (X : Expr) (maxLvl : Level) : MetaM Expr := do
  let whnfX ← whnf X
  match whnfX.getAppFn with
  | Expr.const ``Prod _ =>
    let args := whnfX.getAppArgs
    let a1 := args[0]!
    let a2 ← decomposeProductToSFinker args[1]! maxLvl
    let sfinkerOf1 := Expr.const `SFinKer.of [maxLvl]
    let t1 ← mkAppOptM' sfinkerOf1 #[a1, none]
    mkAppM ``MonoidalCategoryStruct.tensorObj #[t1, a2]
  | _ =>
    let sfinkerOfX := Expr.const `SFinKer.of [maxLvl]
    mkAppOptM' sfinkerOfX #[X, none]

/-- Compute the `SFinKer` object corresponding to a measurable space. -/
def compute_SFinkerOf (X : Expr) (xLvl maxLvl : Level) : MetaM Expr := do
  match ← whnf X with
  | Expr.const ``PUnit _ | Expr.const ``Unit _ =>
    let sfinker := Expr.const `SFinKer [maxLvl]
    let tensorunit :=
      Expr.const ``MonoidalCategoryStruct.tensorUnit [maxLvl, maxLvl.succ]
    mkAppOptM' tensorunit #[sfinker, none, none]
  | _ =>
    let ex ← inferType (← construct_measurable_equiv X xLvl maxLvl)
    let lifted_X := ex.getAppArgs[0]!
    decomposeProductToSFinker lifted_X maxLvl

/-- Construct the left or right unitor morphism. -/
def construct_unitors (X Y : Expr) (yLvl maxLvl : Level) (offset : Nat) :
  MetaM (Expr × CategoryOP) := do
  let left ← if offset == 0 then pure true
    else if offset == 1 then pure false
    else throwError "Invalid offset for unitors"
  let punit_level ← match (← whnf X).getAppFn with
  | Expr.const ``Prod univs => pure univs[offset]!
  | _ =>
    if left then throwError "Expected left unitor with source PUnit × X, got: {X}"
    else throwError "Expected right unitor with source X × PUnit, got: {X}"
  let sfinkerOf ← compute_SFinkerOf Y yLvl maxLvl
  let unitor ← if left then mkAppM ``MonoidalCategoryStruct.leftUnitor #[sfinkerOf]
    else mkAppM ``MonoidalCategoryStruct.rightUnitor #[sfinkerOf]
  let ey ← construct_measurable_equiv Y yLvl maxLvl
  let unitorOP := if left then .leftUnitor_hom punit_level ey
    else .rightUnitor_hom punit_level ey
  return (← mkAppM ``Iso.hom #[unitor], unitorOP)

/-- Check if a kernel expression corresponds to a left or right whisker. -/
def check_Whiskers (κ : Expr) (offset : Nat) : MetaM Bool := do
  let κ := κ.consumeMData
  let args := κ.getAppArgs
  let idKernel := args[args.size - offset]!
  if !idKernel.getAppFn.isConstOf ``Kernel.id then
    return false
  else return true

/-- Check if a kernel expression corresponds to a left whisker. -/
def check_WhiskerLeft (κ : Expr) : MetaM Bool := check_Whiskers κ 2

/-- Check if a kernel expression corresponds to a right whisker. -/
def check_WhiskerRight (κ : Expr) : MetaM Bool := check_Whiskers κ 1

/-- Construct the relevant data for converting a kernel expression to its whisker morphism
representation. -/
def construct_whiskers_args (e X : Expr) (maxLvl : Level) (offset : Nat) :
    MetaM (Expr × Expr × Expr × Level) := do
  let left ← if offset == 0 then pure true
    else if offset == 1 then pure false
    else throwError "Invalid offset for whiskers"
  let whnfX ← whnf X
  let (Z, zLvl) ← match whnfX.getAppFn with
  | Expr.const ``Prod univs =>
    let args := whnfX.getAppArgs
    pure (args[offset]!, univs[offset]!)
  | _ =>
    if left then throwError "Expected left whisker with source Z × X, got: {X}"
    else throwError "Expected right whisker with source X × Z, got: {X}"
  let sfinkerOfZ ← compute_SFinkerOf Z zLvl maxLvl
  let κ ← match e.getAppFn with
    | Expr.const ``Kernel.parallelComp _ =>
      let args := e.getAppArgs
      pure args[args.size - (offset + 1)]!
    | _ =>
      if left then throwError "Expected left whisker with parallelComp, got: {e}"
      else throwError "Expected right whisker with parallelComp, got: {e}"
  return (sfinkerOfZ, κ, Z, zLvl)

def check_associator (κ : Expr) (hom : Bool) : MetaM Bool := do
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

def check_associator_hom (κ : Expr) : MetaM Bool := check_associator κ true

def check_associator_inv (κ : Expr) : MetaM Bool := check_associator κ false

def get_types_from_three_prod (prod : Expr) :
    MetaM (Expr × Expr × Expr × Level × Level × Level) := do
  let whnfprod ← whnf prod
  match whnfprod.getAppFn with
  | Expr.const ``Prod univs =>
    let X := whnfprod.getAppArgs[0]!
    match whnfprod.getAppArgs[1]!.getAppFn with
    | Expr.const ``Prod univs_right =>
      let Y := whnfprod.getAppArgs[1]!.getAppArgs[0]!
      let Z := whnfprod.getAppArgs[1]!.getAppArgs[1]!
      return (X, Y, Z, univs[0]!, univs_right[0]!, univs_right[1]!)
    | _ => throwError "Expected a product of two types, got: {whnfprod.getAppArgs[1]!}"
  | _ => throwError "Expected a product of three types, got: {prod}"

def construct_associator (left right : Expr) (maxLvl : Level) (hom : Bool) :
    MetaM (Expr × CategoryOP) := do
  let (X, Y, Z, xLvl, yLvl, zLvl) ← if hom then get_types_from_three_prod right
    else get_types_from_three_prod left
  let SFinkerOfX ← compute_SFinkerOf X xLvl maxLvl
  let SFinkerOfY ← compute_SFinkerOf Y yLvl maxLvl
  let SFinkerOfZ ← compute_SFinkerOf Z zLvl maxLvl
  let associator ← mkAppM ``MonoidalCategoryStruct.associator #[SFinkerOfX, SFinkerOfY, SFinkerOfZ]
  let ex ← construct_measurable_equiv X xLvl maxLvl
  let ey ← construct_measurable_equiv Y yLvl maxLvl
  let ez ← construct_measurable_equiv Z zLvl maxLvl
  let associatorOP : CategoryOP := if hom then .Associator_hom ex ey ez
    else .Associator_inv ex ey ez
  return (← mkAppM (if hom then ``Iso.hom else ``Iso.inv) #[associator], associatorOP)

def construct_associator_hom (left right : Expr) (maxLvl : Level) :=
  construct_associator left right maxLvl true

def construct_associator_inv (left right : Expr) (maxLvl : Level) :=
  construct_associator left right maxLvl false

/-- Recursive transformation from kernel expressions to morphism expressions in the `SFinKer`
category. -/
-- ANCHOR: transformKernelToHom
partial def transformKernelToHom (maxLvl : Level) (e : Expr) (op_data : List CategoryOP) :
    MetaM (Expr × List CategoryOP) := do
  match e.getAppFn with
  | Expr.const ``Kernel.comp _ =>
    let args := e.getAppArgs
    let κ := args[args.size - 2]!
    let η := args[args.size - 1]!
    let (η', lη) ← transformKernelToHom maxLvl η op_data
    let (κ', lκ) ← transformKernelToHom maxLvl κ lη
    return (← mkAppM ``CategoryStruct.comp #[η', κ'], lκ)
  | Expr.const ``Kernel.monoComp _ =>
    let args := e.getAppArgs
    let κ := args[args.size - 4]!
    let η := args[args.size - 2]!
    let (_, X, _, xLvl) ← get_types_from_kernel κ
    let (Y, _, yLvl, _) ← get_types_from_kernel η
    let (κ', lκ) ← transformKernelToHom maxLvl κ op_data
    let (η', lη) ← transformKernelToHom maxLvl η lκ
    let ex ← construct_measurable_equiv X xLvl maxLvl
    let ey ← construct_measurable_equiv Y yLvl maxLvl
    let monoComp := Expr.const ``monoidalComp [maxLvl, maxLvl.succ]
    let monoCoherenceConst := Expr.const `MeasurableCoherence.monoidalCoherence
      [maxLvl, xLvl, yLvl]
    let monoCoherence ← mkAppOptM' monoCoherenceConst
      #[none, none, none, none, none, none, none, none, none, ex, ey]
    return (← mkAppOptM' monoComp
      #[none, none, none, none, none, none, monoCoherence, κ', η'], lη)
  | Expr.const ``Kernel.parallelComp _ =>
    let (X, _, _, _) ← get_types_from_kernel e
    if ← check_WhiskerLeft e then
      let (sfinkerOfZ, κ, Z, zLvl) ← construct_whiskers_args e X maxLvl 0
      let (κ', lκ) ← transformKernelToHom maxLvl κ op_data
      let whiskerleft ← mkAppM ``MonoidalCategoryStruct.whiskerLeft #[sfinkerOfZ, κ']
      let ez ← construct_measurable_equiv Z zLvl maxLvl
      let leftWhiskerOP := .WhiskerLeft ez
      return (whiskerleft, leftWhiskerOP :: lκ)
    else if ← check_WhiskerRight e then
      let (sfinkerOfZ, κ, Z, zLvl) ← construct_whiskers_args e X maxLvl 1
      let (κ', lκ) ← transformKernelToHom maxLvl κ op_data
      let whiskerleft ← mkAppM ``MonoidalCategoryStruct.whiskerRight #[κ', sfinkerOfZ]
      let ez ← construct_measurable_equiv Z zLvl maxLvl
      let rightWhiskerOP := .WhiskerRight ez
      return (whiskerleft, rightWhiskerOP :: lκ)
    else
      let args := e.getAppArgs
      let κ := args[args.size - 2]!
      let η := args[args.size - 1]!
      let (κ', lκ) ← transformKernelToHom maxLvl κ op_data
      let (η', lη) ← transformKernelToHom maxLvl η lκ
      return (← mkAppM ``MonoidalCategoryStruct.tensorHom #[κ', η'], lη)
  | Expr.const ``Kernel.id _ =>
    let (X, _, xLvl, _) ← get_types_from_kernel e
    let sfinkerOfX ← compute_SFinkerOf X xLvl maxLvl
    let ex ← construct_measurable_equiv X xLvl maxLvl
    let idOP := .id ex
    return (← mkAppM ``CategoryStruct.id #[sfinkerOfX], idOP :: op_data)
  | Expr.const ``Kernel.swap univs =>
    let args := e.getAppArgs
    let X := args[0]!
    let Y := args[1]!
    let xLvl := univs[0]!
    let yLvl := univs[1]!
    let sfinkerOfX ← compute_SFinkerOf X xLvl maxLvl
    let sfinkerOfY ← compute_SFinkerOf Y yLvl maxLvl
    let ex ← construct_measurable_equiv X xLvl maxLvl
    let ey ← construct_measurable_equiv Y yLvl maxLvl
    let braiding ← mkAppM ``Iso.hom #[← mkAppM ``BraidedCategory.braiding #[sfinkerOfX, sfinkerOfY]]
    return (braiding, .Braiding_hom ex ey :: op_data)
  | Expr.const ``Kernel.discard _ =>
    let (X, _, xLvl, _) ← get_types_from_kernel e
    let sfinkerOfX ← compute_SFinkerOf X xLvl maxLvl
    let ex ← construct_measurable_equiv X xLvl maxLvl
    let discardOP := .Counit ex
    return (← mkAppOptM ``ComonObj.counit #[none, none, none, sfinkerOfX, none],
      discardOP :: op_data)
  | Expr.const ``Kernel.copy _ =>
    let (X, _, xLvl, _) ← get_types_from_kernel e
    let sfinkerOfX ← compute_SFinkerOf X xLvl maxLvl
    let ex ← construct_measurable_equiv X xLvl maxLvl
    let copyOP := .Comul ex
    return (← mkAppOptM ``ComonObj.comul #[none, none, none, sfinkerOfX, none],
      copyOP :: op_data)
  | _ =>
    let (X, Y, xLvl, yLvl) ← get_types_from_kernel e
    if ← check_leftUnitor e then
      let (leftUnitorExpr, leftUnitorOP) ← construct_unitors X Y yLvl maxLvl 0
      return (leftUnitorExpr, leftUnitorOP :: op_data)
    else if ← check_rightUnitor e then
      let (rightUnitorExpr, rightUnitorOP) ← construct_unitors X Y yLvl maxLvl 1
      return (rightUnitorExpr, rightUnitorOP :: op_data)
    else if ← check_associator_hom e then
      let (associatorExpr, associatorOP) ← construct_associator_hom X Y maxLvl
      return (associatorExpr, associatorOP :: op_data)
    else if ← check_associator_inv e then
      let (associatorExpr, associatorOP) ← construct_associator_inv X Y maxLvl
      return (associatorExpr, associatorOP :: op_data)
    else
      let quiverConst := Expr.const ``Kernel.hom [maxLvl, xLvl, yLvl]
      let ex ← construct_measurable_equiv X xLvl maxLvl
      let ey ← construct_measurable_equiv Y yLvl maxLvl
      return( ← mkAppOptM' quiverConst
        #[none, none, none, none, none, none, none, none, ex, ey, e, none], op_data)
-- ANCHOR_END: transformKernelToHom

/-- Construct the proof of equivalence between the original equality and the transformed one. -/
def mkKernelHomEqProof (eqProofType rhs lhs : Expr) (maxLvl : Level)
    (op_data : List CategoryOP) : TacticM Expr := do
  let maxLvlStx ← liftMacroM <| levelToSyntax maxLvl
  let rhsStx ← Term.exprToSyntax rhs
  let lhsStx ← Term.exprToSyntax lhs
  let op_data := op_data.reverse
  let savedGoals ← getGoals
  let mvar ← mkFreshExprSyntheticOpaqueMVar eqProofType
  let mvarId := mvar.mvarId!
  setGoals [mvarId]
  evalTactic (← `(tactic| apply propext))
  evalTactic (← `(tactic| constructor))
  let goalsAfterConstructor ← getGoals
  match goalsAfterConstructor with
  | [forwardGoal, backwardGoal] =>
    setGoals [forwardGoal]
    evalTactic (← `(tactic| intro h))
    evalTactic (← `(tactic| try dsimp only [MonoidalCategoryStruct.tensorUnit,
      MonoidalCategoryStruct.tensorObj]))
    for e in op_data do
      match e with
      | .leftUnitor_hom lvl equiv =>
        let punitLevelStx ← liftMacroM <| levelToSyntax lvl
        let eStx ← Term.exprToSyntax equiv
        evalTactic (← `(tactic| nth_rw 1 [Kernel.leftUnitor_hom.{_, _, $punitLevelStx}
          (ex := $eStx)]))
      | .rightUnitor_hom lvl equiv =>
        let punitLevelStx ← liftMacroM <| levelToSyntax lvl
        let eStx ← Term.exprToSyntax equiv
        evalTactic (← `(tactic| nth_rw 1 [Kernel.rightUnitor_hom.{_, _, $punitLevelStx}
          (ex := $eStx)]))
      | .id equiv =>
        let eStx ← Term.exprToSyntax equiv
        evalTactic (← `(tactic| nth_rw 1 [Kernel.hom_id (ex := $eStx)]))
      | .Associator_hom ex ey ez =>
        let exStx ← Term.exprToSyntax ex
        let eyStx ← Term.exprToSyntax ey
        let ezStx ← Term.exprToSyntax ez
        evalTactic (← `(tactic| nth_rw 1 [Kernel.associator_hom (ex := $exStx) (ey := $eyStx)
          (ez := $ezStx)]))
      | .Associator_inv ex ey ez =>
        let exStx ← Term.exprToSyntax ex
        let eyStx ← Term.exprToSyntax ey
        let ezStx ← Term.exprToSyntax ez
        evalTactic (← `(tactic| nth_rw 1 [Kernel.associator_inv (ex := $exStx) (ey := $eyStx)
          (ez := $ezStx)]))
      | .Braiding_hom ex ey =>
        let exStx ← Term.exprToSyntax ex
        let eyStx ← Term.exprToSyntax ey
        evalTactic (← `(tactic| nth_rw 1 [Kernel.braiding_hom (ex := $exStx)
          (ey := $eyStx)]))
      | .Counit equiv =>
        let eStx ← Term.exprToSyntax equiv
        evalTactic (← `(tactic| nth_rw 1 [Kernel.counit (ex := $eStx)]))
      | .Comul equiv =>
        let eStx ← Term.exprToSyntax equiv
        evalTactic (← `(tactic| nth_rw 1 [Kernel.comul (ex := $eStx)]))
      | _ => pure ()
    let congr_tac ← `(tactic| simp only [
        Kernel.hom_monoComp.{$maxLvlStx},
        Kernel.hom_comp.{$maxLvlStx},
        Kernel.tensorHom.{$maxLvlStx},
      ]
    )
    if !(← getGoals).isEmpty then
      try
        evalTactic congr_tac
      catch _ =>
        pure ()
      for e in op_data do
        match e with
        | .WhiskerLeft equiv =>
          let eStx ← Term.exprToSyntax equiv
          evalTactic (← `(tactic| nth_rw 1 [Kernel.WhiskerLeft (ez := $eStx)]))
          try
            evalTactic congr_tac
          catch _ =>
            pure ()
        | .WhiskerRight equiv =>
          let eStx ← Term.exprToSyntax equiv
          evalTactic (← `(tactic| nth_rw 1 [Kernel.WhiskerRight (ez := $eStx)]))
          try
            evalTactic congr_tac
          catch _ =>
            pure ()
        | _ => pure ()
      evalTactic (← `(tactic| rwa [Kernel.quiver_congr.{$maxLvlStx}
        (κ₁ := $rhsStx) (κ₂ := $lhsStx)]))

    setGoals [backwardGoal]
    evalTactic (← `(tactic| intro h))
    evalTactic (← `(tactic| try dsimp only [MonoidalCategory.tensorUnit,
      MonoidalCategoryStruct.tensorObj] at h))
    for e in op_data do
      match e with
      | .leftUnitor_hom lvl equiv =>
        let punitLevelStx ← liftMacroM <| levelToSyntax lvl
        let eStx ← Term.exprToSyntax equiv
        evalTactic (← `(tactic| nth_rw 1 [Kernel.leftUnitor_hom.{_, _, $punitLevelStx}
          (ex := $eStx)] at h))
      | .rightUnitor_hom lvl equiv =>
        let punitLevelStx ← liftMacroM <| levelToSyntax lvl
        let eStx ← Term.exprToSyntax equiv
        evalTactic (← `(tactic| nth_rw 1 [Kernel.rightUnitor_hom.{_, _, $punitLevelStx}
          (ex := $eStx)] at h))
      | .id equiv =>
        let eStx ← Term.exprToSyntax equiv
        evalTactic (← `(tactic| nth_rw 1 [Kernel.hom_id (ex := $eStx)] at h))
      | .Associator_hom ex ey ez =>
        let exStx ← Term.exprToSyntax ex
        let eyStx ← Term.exprToSyntax ey
        let ezStx ← Term.exprToSyntax ez
        evalTactic (← `(tactic| nth_rw 1 [Kernel.associator_hom (ex := $exStx) (ey := $eyStx)
          (ez := $ezStx)] at h))
      | .Associator_inv ex ey ez =>
        let exStx ← Term.exprToSyntax ex
        let eyStx ← Term.exprToSyntax ey
        let ezStx ← Term.exprToSyntax ez
        evalTactic (← `(tactic| nth_rw 1 [Kernel.associator_inv (ex := $exStx) (ey := $eyStx)
          (ez := $ezStx)] at h))
      | .Braiding_hom ex ey =>
        let exStx ← Term.exprToSyntax ex
        let eyStx ← Term.exprToSyntax ey
        evalTactic (← `(tactic| nth_rw 1 [Kernel.braiding_hom (ex := $exStx)
          (ey := $eyStx)] at h))
      | .Counit equiv =>
        let eStx ← Term.exprToSyntax equiv
        evalTactic (← `(tactic| nth_rw 1 [Kernel.counit (ex := $eStx)] at h))
      | .Comul equiv =>
        let eStx ← Term.exprToSyntax equiv
        evalTactic (← `(tactic| nth_rw 1 [Kernel.comul (ex := $eStx)] at h))
      | _ => pure ()
    if !(← getGoals).isEmpty then
      let congr_tac ← `(tactic| simp only [
          Kernel.hom_monoComp.{$maxLvlStx},
          Kernel.hom_comp.{$maxLvlStx},
          Kernel.tensorHom.{$maxLvlStx},
        ] at h
      )
      try
        evalTactic congr_tac
      catch _ =>
        pure ()
      for e in op_data do
        match e with
        | .WhiskerLeft equiv =>
          let eStx ← Term.exprToSyntax equiv
          evalTactic (← `(tactic| nth_rw 1 [Kernel.WhiskerLeft (ez := $eStx)] at h))
          try
            evalTactic congr_tac
          catch _ =>
            pure ()
        | .WhiskerRight equiv =>
          let eStx ← Term.exprToSyntax equiv
          evalTactic (← `(tactic| nth_rw 1 [Kernel.WhiskerRight (ez := $eStx)] at h))
          try
            evalTactic congr_tac
          catch _ =>
            pure ()
        | _ => pure ()
      evalTactic (← `(tactic| rwa [Kernel.quiver_congr.{$maxLvlStx} (κ₁ := $rhsStx)
        (κ₂ := $lhsStx)] at h))
  | _ =>
    setGoals savedGoals
    throwError "Expected exactly two goals after `constructor`"

  if !(← getGoals).isEmpty then
    setGoals savedGoals
    throwError "Failed to solve all goals while building kernel_hom equivalence proof"

  setGoals savedGoals
  instantiateMVars mvar

/-- Core implementation of the `kernel_hom` tactic on a single goal or hypothesis. -/
def applyKernelHom (goal : MVarId) (fvarId : Option FVarId) : TacticM MVarId := do
  goal.withContext do
    let expr ← match fvarId with
        | some fid => do
          let decl ← fid.getDecl
          pure decl.type
        | none => goal.getType
    let maxLvl ← compute_max_universe (← collectExprUniverses expr)
    let (homExpr, op_data, rhs, lhs) ← transformEquality maxLvl expr transformKernelToHom
    let eqProofType ← mkEq expr homExpr
    let eqProof ← mkKernelHomEqProof eqProofType rhs lhs maxLvl op_data
    match fvarId with
    | some fid => do
      let mvarId ← getMainGoal
      let hProof ← mkEqMP eqProof (mkFVar fid)
      let userName := (← fid.getDecl).userName
      let mvarId ← mvarId.assert userName homExpr hProof
      let mvarId ← mvarId.tryClear fid
      let (_, mvarId) ← mvarId.intro1P
      pure mvarId
    | none => do
      let mvarId ← getMainGoal
      mvarId.replaceTargetEq homExpr eqProof

/-- The `kernel_hom` tactic transforms a kernel equality to an equivalent equality in
the category of measurable spaces and s-finite kernels.

The tactic supports location specifiers like `rw` or `simp`:
- `kernel_hom` — applies to the goal
- `kernel_hom at h` — applies to hypothesis `h`
- `kernel_hom at h₁ h₂` — applies to multiple hypotheses
- `kernel_hom at h ⊢` — applies to hypothesis `h` and the goal
- `kernel_hom at *` — applies to all hypotheses and the goal

Example:
```lean
example {W X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    [MeasurableSpace W] (κ : Kernel X Y) (η : Kernel Y Z) (ξ : Kernel Z W)
    [IsFiniteKernel ξ] [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    ξ ∘ₖ (η ∘ₖ κ) = ξ ∘ₖ η ∘ₖ κ := by
  kernel_hom
  exact Category.assoc _ _ _
``` -/
syntax "kernel_hom" (ppSpace location)? : tactic

-- ANCHOR: kernel_hom_tactic
elab_rules : tactic
  | `(tactic| kernel_hom $[$loc]?) =>
    expandOptLocation (Lean.mkOptionalNode loc) |> applyLocTactic <| applyKernelHom
-- ANCHOR_END: kernel_hom_tactic

variable {W X Y Z : Type*} [MeasurableSpace W] [MeasurableSpace X] [MeasurableSpace Y]
[MeasurableSpace Z]

variable (κ : Kernel X Y) (η : Kernel Y Z) (ξ : Kernel Z W)
    [IsFiniteKernel ξ] [IsSFiniteKernel κ] [IsSFiniteKernel η]

-- ANCHOR: example_kernel_hom1
example : ξ ∘ₖ (η ∘ₖ κ) = ξ ∘ₖ η ∘ₖ κ := by
  kernel_hom
  simp only [Category.assoc]
-- ANCHOR_END: example_kernel_hom1

-- ANCHOR: example_kernel_hom2
example : (η ∘ₖ Kernel.id.map (Prod.fst : Y × PUnit → Y)) ∘ₖ
    (Kernel.id.map (Prod.fst : Y × PUnit → Y) ∥ₖ Kernel.id (α := PUnit)) ∘ₖ
      ((κ ∥ₖ Kernel.id (α := PUnit)) ∥ₖ Kernel.id (α := PUnit))
    = (η ∘ₖ κ ∘ₖ (Kernel.id.map (Prod.fst : X × PUnit → X)) ∘ₖ
      ((Kernel.id.map (Prod.fst : X × PUnit → X)) ∥ₖ Kernel.id (α := PUnit))
    : Kernel ((X × PUnit) × PUnit) Z)
     := by
  kernel_hom; monoidal
-- ANCHOR_END: example_kernel_hom2
