/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import KernelHom.Tactic.Hom.KernelHom

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

/-- Get the original type and its universe from a `SFinKer.of` expression. -/
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
    | _ => throwError "Expected a type with a universe level ≥ 0, got: {e}"

/-- Deconstruct a left or right unitor morphism to get the underlying kernel -/
def deconstructUnitorsHom (iso : Expr) (eLevel : Level) (left : Bool) :
    MetaM (Expr × CategoryOP) := do
  let iso_t ← inferType iso
  let SX := iso_t.getAppArgs[3]!
  let (X, xLvl) ← getTypeFromSFinKer SX
  let kernel_id ←
    if left then
      let UnitX ← mkAppOptM' (Expr.const ``Prod [Level.zero, xLvl]) #[Expr.const ``Unit [], X]
      let mUnitX ← synthInstance (mkApp (Expr.const ``MeasurableSpace [xLvl]) UnitX)
      mkAppOptM ``Kernel.id #[UnitX, mUnitX]
    else
      let XUnit ← mkAppOptM' (Expr.const ``Prod [xLvl, Level.zero]) #[X, Expr.const ``Unit []]
      let mXUnit ← synthInstance (mkApp (Expr.const ``MeasurableSpace [xLvl]) XUnit)
      mkAppOptM ``Kernel.id #[XUnit, mXUnit]
  let prod ← if left then
      mkAppOptM ``Prod.snd #[Expr.const ``Unit [], X]
    else
      mkAppOptM ``Prod.fst #[X, Expr.const ``Unit []]
  let ex ← constructMeasurableEquiv X xLvl eLevel
  let OP := if left then .leftUnitor_hom xLvl SX ex else .rightUnitor_hom xLvl SX ex
  return (← mkAppM ``Kernel.map #[kernel_id, prod], OP)

/-- Deconstruct a left or right unitor inverse morphism to get the underlying kernel -/
def deconstructUnitorsInv (iso : Expr) (eLevel : Level) (left : Bool) :
    MetaM (Expr × CategoryOP) := do
  let iso_t ← inferType iso
  let SX := iso_t.getAppArgs[3]!
  let (X, xLvl) ← getTypeFromSFinKer SX
  let kernel_id ← do
    let mX ← synthInstance (mkApp (Expr.const ``MeasurableSpace [xLvl]) X)
    mkAppOptM ``Kernel.id #[X, mX]
  let f :=
    if left then
      Expr.lam `x X (
        (((.const ``Prod.mk [Level.zero, xLvl] |> Expr.app <| .const ``Unit [])
        |> Expr.app <| X) |> Expr.app <| .const ``Unit.unit []) |> Expr.app <| .bvar 0
      ) .default
    else
      Expr.lam `x X (
        (((.const ``Prod.mk [xLvl, Level.zero] |> Expr.app <| X) |> Expr.app
        <| .const ``Unit []) |> Expr.app <| .bvar 0) |> Expr.app <| .const ``Unit.unit []
      ) .default
  let ex ← constructMeasurableEquiv X xLvl eLevel
  let OP := if left then .leftUnitor_inv xLvl SX ex else .rightUnitor_inv xLvl SX ex
  return (← mkAppM ``Kernel.map #[kernel_id, f], OP)

/-- Deconstruct the associator morphism to get the underlying kernel -/
def deconstructAssociatorHom (iso : Expr) (eLevel : Level) : MetaM (Expr × CategoryOP) := do
  let args := iso.getAppArgs
  let SX := args[args.size - 3]!
  let SY := args[args.size - 2]!
  let SZ := args[args.size - 1]!
  let (X, xLvl) ← getTypeFromSFinKer SX
  let (Y, yLvl) ← getTypeFromSFinKer SY
  let (Z, zLvl) ← getTypeFromSFinKer SZ
  let mequiv_prodassoc ← mkAppOptM ``MeasurableEquiv.prodAssoc #[X, Y, Z, none, none, none]
  let measurable_instance ← mkAppM ``MeasurableEquiv.measurable #[mequiv_prodassoc]
  let dfuncoe ← mkAppM ``DFunLike.coe #[mequiv_prodassoc]
  let kernel_deterministic ← mkAppM ``Kernel.deterministic #[dfuncoe, measurable_instance]
  let ex ← constructMeasurableEquiv X xLvl eLevel
  let ey ← constructMeasurableEquiv Y yLvl eLevel
  let ez ← constructMeasurableEquiv Z zLvl eLevel
  let OP := .Associator_hom SX ex SY ey SZ ez
  return (kernel_deterministic, OP)

/-- Deconstruct the associator inverse morphism to get the underlying kernel -/
def deconstructAssociatorInv (iso : Expr) (eLevel : Level) : MetaM (Expr × CategoryOP) := do
  let args := iso.getAppArgs
  let SX := args[args.size - 3]!
  let SY := args[args.size - 2]!
  let SZ := args[args.size - 1]!
  let (X, xLvl) ← getTypeFromSFinKer SX
  let (Y, yLvl) ← getTypeFromSFinKer SY
  let (Z, zLvl) ← getTypeFromSFinKer SZ
  let mequiv_prodassoc ← mkAppM ``MeasurableEquiv.symm
    #[← mkAppOptM ``MeasurableEquiv.prodAssoc #[X, Y, Z, none, none, none]]
  let measurable_instance ← mkAppM ``MeasurableEquiv.measurable #[mequiv_prodassoc]
  let dfuncoe ← mkAppM ``DFunLike.coe #[mequiv_prodassoc]
  let kernel_deterministic ← mkAppM ``Kernel.deterministic #[dfuncoe, measurable_instance]
  let ex ← constructMeasurableEquiv X xLvl eLevel
  let ey ← constructMeasurableEquiv Y yLvl eLevel
  let ez ← constructMeasurableEquiv Z zLvl eLevel
  let OP := .Associator_inv SX ex SY ey SZ ez
  return (kernel_deterministic, OP)

/-- Deconstruct the braiding morphism to get the underlying swapped objects -/
def deconstructBraiding (iso : Expr) (eLevel : Level) :
    MetaM (Expr × Expr × Expr × Expr × Expr × Expr) := do
  let args := iso.getAppArgs
  let SX := args[args.size - 2]!
  let SY := args[args.size - 1]!
  let (X, xLvl) ← getTypeFromSFinKer SX
  let (Y, yLvl) ← getTypeFromSFinKer SY
  let ex ← constructMeasurableEquiv X xLvl eLevel
  let ey ← constructMeasurableEquiv Y yLvl eLevel
  return (X, Y, SX, ex, SY, ey)

/-- Deconstruct a left or right whisker to get the underlying kernel and the whiskered object -/
def deconstructWhiskersHomArgs (e : Expr) (eLevel : Level) (left : Bool) :
    MetaM (Expr × Expr × CategoryOP) := do
  let args := e.getAppArgs
  let SX := if left then args[args.size - 4]! else args[args.size - 1]!
  let κ := if left then args[args.size - 1]! else args[args.size - 2]!
  let (X, xLvl) ← getTypeFromSFinKer SX
  let mXUnit ← synthInstance (mkApp (Expr.const ``MeasurableSpace [xLvl]) X)
  let kernel_id ← mkAppOptM ``Kernel.id #[X, mXUnit]
  let ex ← constructMeasurableEquiv X xLvl eLevel
  let OP := if left then .WhiskerLeft SX ex else .WhiskerRight SX ex
  return (κ, kernel_id, OP)

/-- Recursive transformation from morphism expression in `SFinKer` to kernel expression. -/
partial def transformHomToKernel (eLevel : Level) (e : Expr) (op_data : List CategoryOP) :
    MetaM (Expr × List CategoryOP) := do
  match e.getAppFn with
  | Expr.const ``CategoryStruct.id _ =>
    let args := e.getAppArgs
    let X := args[args.size - 1]!
    let (X', xLvl) ← getTypeFromSFinKer X
    let ex ← constructMeasurableEquiv X' xLvl eLevel
    let mX' ← synthInstance (mkApp (Expr.const ``MeasurableSpace [xLvl]) X')
    return (← mkAppOptM ``Kernel.id #[X', mX'], .id X ex :: op_data)
  | Expr.const ``CategoryStruct.comp _ =>
    let args := e.getAppArgs
    let κ := args[args.size - 2]!
    let η := args[args.size - 1]!
    let (κ', lκ) ← transformHomToKernel eLevel κ op_data
    let (η', lη) ← transformHomToKernel eLevel η lκ
    return (← mkAppM ``Kernel.comp #[η', κ'], lη)
  | Expr.const ``monoidalComp _ =>
    let args := e.getAppArgs
    let κ := args[args.size - 2]!
    let η := args[args.size - 1]!
    let (κ', lκ) ← transformHomToKernel eLevel κ op_data
    let (η', lη) ← transformHomToKernel eLevel η lκ
    return (← mkAppOptM ``Kernel.monoComp
      #[none, none, none, none, none, none, none, none, none, κ', none, η', none], lη)
  | Expr.const ``Iso.hom _ =>
    let args := e.getAppArgs
    let iso := args[args.size - 1]!
    match iso.getAppFn with
    | Expr.const ``leftUnitor _ =>
      let (res, leftUnitorOP) ← deconstructUnitorsHom iso eLevel true
      return (res, leftUnitorOP :: op_data)
    | Expr.const ``rightUnitor _ =>
      let (res, rightUnitorOP) ← deconstructUnitorsHom iso eLevel false
      return (res, rightUnitorOP :: op_data)
    | Expr.const ``associator _ =>
      let (res, associatorHomOP) ← deconstructAssociatorHom iso eLevel
      return (res, associatorHomOP :: op_data)
    | Expr.const ``BraidedCategory.braiding _ =>
      let (X, Y, sfinkerOfX, ex, sfinkerOfY, ey) ← deconstructBraiding iso eLevel
      let e ← mkAppOptM ``Kernel.swap #[X, Y, none, none]
      return (e, .Braiding_hom sfinkerOfX ex sfinkerOfY ey :: op_data)
    | _ => throwError "Unexpected isomorphism {iso}"
  | Expr.const ``Iso.inv _ =>
    let args := e.getAppArgs
    let iso := args[args.size - 1]!
    match iso.getAppFn with
    | Expr.const ``leftUnitor _ =>
      let (res, leftUnitorInvOP) ← deconstructUnitorsInv iso eLevel true
      return (res, leftUnitorInvOP :: op_data)
    | Expr.const ``rightUnitor _ =>
      let (res, rightUnitorInvOP) ← deconstructUnitorsInv iso eLevel false
      return (res, rightUnitorInvOP :: op_data)
    | Expr.const ``associator _ =>
      let (res, associatorInvOP) ← deconstructAssociatorInv iso eLevel
      return (res, associatorInvOP :: op_data)
    | Expr.const ``BraidedCategory.braiding _ =>
      let (X, Y, sfinkerOfX, ex, sfinkerOfY, ey) ← deconstructBraiding iso eLevel
      let e ← mkAppOptM ``Kernel.swap #[Y, X, none, none]
      return (e, .Braiding_hom sfinkerOfX ex sfinkerOfY ey :: op_data)
    | _ => throwError "Unexpected isomorphism {iso}"
  | Expr.const ``whiskerLeft _ =>
    let (κ, kernel_id, whiskerLeftOP) ← deconstructWhiskersHomArgs e eLevel true
    let (κ', lκ) ← transformHomToKernel eLevel κ op_data
    let res ← mkAppM ``Kernel.parallelComp #[kernel_id, κ']
    return (res, whiskerLeftOP :: lκ)
  | Expr.const ``whiskerRight _ =>
    let (κ, kernel_id, whiskerRightOP) ← deconstructWhiskersHomArgs e eLevel false
    let (κ', lκ) ← transformHomToKernel eLevel κ op_data
    return (← mkAppM ``Kernel.parallelComp #[κ', kernel_id], whiskerRightOP :: lκ)
  | Expr.const ``tensorHom _ =>
    let args := e.getAppArgs
    let κ := args[args.size - 2]!
    let η := args[args.size - 1]!
    let (κ', lκ) ← transformHomToKernel eLevel κ op_data
    let (η', lη) ← transformHomToKernel eLevel η lκ
    return (← mkAppM ``Kernel.parallelComp #[κ', η'], lη)
  | Expr.const ``ComonObj.counit _ =>
    let args := e.getAppArgs
    let SX := args[args.size - 2]!
    let (X, xLvl) ← getTypeFromSFinKer SX
    let ex ← constructMeasurableEquiv X xLvl eLevel
    let discard_kernel_const := Expr.const ``Kernel.discard [xLvl, Level.zero]
    return (← mkAppOptM' discard_kernel_const #[X, none], .Counit SX ex :: op_data)
  | Expr.const ``ComonObj.comul _ =>
    let args := e.getAppArgs
    let SX := args[args.size - 2]!
    let (X, xLvl) ← getTypeFromSFinKer SX
    let ex ← constructMeasurableEquiv X xLvl eLevel
    return (← mkAppOptM ``Kernel.copy #[X, none], .Comul SX ex :: op_data)
  | Expr.const ``Kernel.hom _ =>
    let args := e.getAppArgs
    let κ := args[args.size - 2]!
    return (κ, op_data)
  | _ => throwError "Expected a hom expression, got: {e}"

/-- Construct the proof of equivalence between the original equality and the transformed one. -/
def mkHomKernelEqProof (eqProofType : Expr) (eLevel : Level)
    (op_data : List CategoryOP) : TacticM Expr := do
  let eLevelStx ← liftMacroM <| levelToSyntax eLevel
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
    for e in op_data do
      match e with
      | .leftUnitor_hom _ sfinker equiv =>
        let sfinkerStx ← Term.exprToSyntax sfinker
        let equivStx ← Term.exprToSyntax equiv
        evalTactic (← `(tactic| nth_rw 1 [
          Kernel.leftUnitor_hom.{_, _, 0} (X' := $sfinkerStx) (ex := $equivStx)] at h))
      | .leftUnitor_inv _ sfinker equiv =>
        let sfinkerStx ← Term.exprToSyntax sfinker
        let equivStx ← Term.exprToSyntax equiv
        evalTactic (← `(tactic| nth_rw 1 [
          Kernel.leftUnitor_inv.{_, _, 0} (X' := $sfinkerStx) (ex := $equivStx)] at h))
      | .rightUnitor_hom _ sfinker equiv =>
        let sfinkerStx ← Term.exprToSyntax sfinker
        let equivStx ← Term.exprToSyntax equiv
        evalTactic (← `(tactic| nth_rw 1 [
          Kernel.rightUnitor_hom.{_, _, 0} (X' := $sfinkerStx) (ex := $equivStx)] at h))
      | .rightUnitor_inv _ sfinker equiv =>
        let sfinkerStx ← Term.exprToSyntax sfinker
        let equivStx ← Term.exprToSyntax equiv
        evalTactic (← `(tactic| nth_rw 1 [
          Kernel.rightUnitor_inv.{_, _, 0} (X' := $sfinkerStx) (ex := $equivStx)] at h))
      | .id sfinker equiv =>
        let sfinkerStx ← Term.exprToSyntax sfinker
        let equivStx ← Term.exprToSyntax equiv
        evalTactic (← `(tactic| nth_rw 1 [
          Kernel.hom_id (X' := $sfinkerStx) (ex := $equivStx)] at h))
      | .Associator_hom sfinkerX equivX sfinkerY equivY sfinkerZ equivZ =>
        let sfinkerXStx ← Term.exprToSyntax sfinkerX
        let equivXStx ← Term.exprToSyntax equivX
        let sfinkerYStx ← Term.exprToSyntax sfinkerY
        let equivYStx ← Term.exprToSyntax equivY
        let sfinkerZStx ← Term.exprToSyntax sfinkerZ
        let equivZStx ← Term.exprToSyntax equivZ
        evalTactic (← `(tactic| nth_rw 1 [
          Kernel.associator_hom
          (X' := $sfinkerXStx) (ex := $equivXStx)
          (Y' := $sfinkerYStx) (ey := $equivYStx)
          (Z' := $sfinkerZStx) (ez := $equivZStx)
        ] at h))
      | .Associator_inv sfinkerX equivX sfinkerY equivY sfinkerZ equivZ =>
        let sfinkerXStx ← Term.exprToSyntax sfinkerX
        let equivXStx ← Term.exprToSyntax equivX
        let sfinkerYStx ← Term.exprToSyntax sfinkerY
        let equivYStx ← Term.exprToSyntax equivY
        let sfinkerZStx ← Term.exprToSyntax sfinkerZ
        let equivZStx ← Term.exprToSyntax equivZ
        evalTactic (← `(tactic| nth_rw 1 [
          Kernel.associator_inv
          (X' := $sfinkerXStx) (ex := $equivXStx)
          (Y' := $sfinkerYStx) (ey := $equivYStx)
          (Z' := $sfinkerZStx) (ez := $equivZStx)
        ] at h))
      | .Braiding_hom sfinkerX equivX sfinkerY equivY =>
        let sfinkerXStx ← Term.exprToSyntax sfinkerX
        let equivXStx ← Term.exprToSyntax equivX
        let sfinkerYStx ← Term.exprToSyntax sfinkerY
        let equivYStx ← Term.exprToSyntax equivY
        evalTactic (← `(tactic| nth_rw 1 [
          Kernel.braiding_hom (X' := $sfinkerXStx) (ex := $equivXStx)
          (Y' := $sfinkerYStx) (ey := $equivYStx)] at h))
      | .Counit sfinker equiv =>
        let sfinkerStx ← Term.exprToSyntax sfinker
        let equivStx ← Term.exprToSyntax equiv
        evalTactic (← `(tactic| nth_rw 1 [
          Kernel.counit (X' := $sfinkerStx) (ex := $equivStx)] at h))
      | .Comul sfinker equiv =>
        let sfinkerStx ← Term.exprToSyntax sfinker
        let eStx ← Term.exprToSyntax equiv
        evalTactic (← `(tactic| nth_rw 1 [Kernel.comul (X' := $sfinkerStx) (ex := $eStx)] at h))
      | _ => pure ()
    if !(← getGoals).isEmpty then
      let congr_tac ← `(tactic| simp only [
          Kernel.hom_monoComp.{$eLevelStx},
          Kernel.hom_comp.{$eLevelStx},
          Kernel.tensorHom.{$eLevelStx},
        ] at h
      )
      try
        evalTactic congr_tac
      catch _ =>
        pure ()
      for e in op_data do
        match e with
        | .WhiskerLeft sfinker equiv =>
          let sfinkerStx ← Term.exprToSyntax sfinker
          let equivStx ← Term.exprToSyntax equiv
          evalTactic (← `(tactic| nth_rw 1 [
            Kernel.WhiskerLeft.{$eLevelStx} (Z' := $sfinkerStx) (ez := $equivStx)] at h))
          try
            evalTactic congr_tac
          catch _ =>
            pure ()
        | .WhiskerRight sfinker equiv =>
          let sfinkerStx ← Term.exprToSyntax sfinker
          let equivStx ← Term.exprToSyntax equiv
          evalTactic (← `(tactic| nth_rw 1 [
            Kernel.WhiskerRight.{$eLevelStx} (Z' := $sfinkerStx) (ez := $equivStx)] at h))
          try
            evalTactic congr_tac
          catch _ =>
            pure ()
        | _ => pure ()
      evalTactic (← `(tactic| rwa [Kernel.hom_congr.{$eLevelStx}] at h))

    setGoals [backwardGoal]
    evalTactic (← `(tactic| intro h))
    for e in op_data do
      match e with
      | .leftUnitor_hom _ sfinker equiv =>
        let sfinkerStx ← Term.exprToSyntax sfinker
        let equivStx ← Term.exprToSyntax equiv
        evalTactic (← `(tactic| nth_rw 1 [
          Kernel.leftUnitor_hom.{_, _, 0} (X' := $sfinkerStx) (ex := $equivStx)]))
      | .leftUnitor_inv _ sfinker equiv =>
        let sfinkerStx ← Term.exprToSyntax sfinker
        let equivStx ← Term.exprToSyntax equiv
        evalTactic (← `(tactic| nth_rw 1 [
          Kernel.leftUnitor_inv.{_, _, 0} (X' := $sfinkerStx) (ex := $equivStx)]))
      | .rightUnitor_hom _ sfinker equiv =>
        let sfinkerStx ← Term.exprToSyntax sfinker
        let equivStx ← Term.exprToSyntax equiv
        evalTactic (← `(tactic| nth_rw 1 [
          Kernel.rightUnitor_hom.{_, _, 0} (X' := $sfinkerStx) (ex := $equivStx)]))
      | .rightUnitor_inv _ sfinker equiv =>
        let sfinkerStx ← Term.exprToSyntax sfinker
        let equivStx ← Term.exprToSyntax equiv
        evalTactic (← `(tactic| nth_rw 1 [
          Kernel.rightUnitor_inv.{_, _, 0} (X' := $sfinkerStx) (ex := $equivStx)]))
      | .id sfinker equiv =>
        let sfinkerStx ← Term.exprToSyntax sfinker
        let equivStx ← Term.exprToSyntax equiv
        evalTactic (← `(tactic| nth_rw 1 [
          Kernel.hom_id (X' := $sfinkerStx) (ex := $equivStx)]))
      | .Associator_hom sfinkerX equivX sfinkerY equivY sfinkerZ equivZ =>
        let sfinkerXStx ← Term.exprToSyntax sfinkerX
        let equivXStx ← Term.exprToSyntax equivX
        let sfinkerYStx ← Term.exprToSyntax sfinkerY
        let equivYStx ← Term.exprToSyntax equivY
        let sfinkerZStx ← Term.exprToSyntax sfinkerZ
        let equivZStx ← Term.exprToSyntax equivZ
        evalTactic (← `(tactic| nth_rw 1 [
          Kernel.associator_hom
          (X' := $sfinkerXStx) (ex := $equivXStx)
          (Y' := $sfinkerYStx) (ey := $equivYStx)
          (Z' := $sfinkerZStx) (ez := $equivZStx)
        ]))
      | .Associator_inv sfinkerX equivX sfinkerY equivY sfinkerZ equivZ =>
        let sfinkerXStx ← Term.exprToSyntax sfinkerX
        let equivXStx ← Term.exprToSyntax equivX
        let sfinkerYStx ← Term.exprToSyntax sfinkerY
        let equivYStx ← Term.exprToSyntax equivY
        let sfinkerZStx ← Term.exprToSyntax sfinkerZ
        let equivZStx ← Term.exprToSyntax equivZ
        evalTactic (← `(tactic| nth_rw 1 [
          Kernel.associator_inv
          (X' := $sfinkerXStx) (ex := $equivXStx)
          (Y' := $sfinkerYStx) (ey := $equivYStx)
          (Z' := $sfinkerZStx) (ez := $equivZStx)
        ]))
      | .Braiding_hom sfinkerX equivX sfinkerY equivY =>
        let sfinkerXStx ← Term.exprToSyntax sfinkerX
        let equivXStx ← Term.exprToSyntax equivX
        let sfinkerYStx ← Term.exprToSyntax sfinkerY
        let equivYStx ← Term.exprToSyntax equivY
        evalTactic (← `(tactic| nth_rw 1 [
          Kernel.braiding_hom (X' := $sfinkerXStx) (ex := $equivXStx)
          (Y' := $sfinkerYStx) (ey := $equivYStx)]))
      | .Counit sfinker equiv =>
        let sfinkerStx ← Term.exprToSyntax sfinker
        let equivStx ← Term.exprToSyntax equiv
        evalTactic (← `(tactic| nth_rw 1 [
          Kernel.counit (X' := $sfinkerStx) (ex := $equivStx)]))
      | .Comul sfinker equiv =>
        let sfinkerStx ← Term.exprToSyntax sfinker
        let eStx ← Term.exprToSyntax equiv
        evalTactic (← `(tactic| nth_rw 1 [Kernel.comul (X' := $sfinkerStx) (ex := $eStx)]))
      | _ => pure ()

    if !(← getGoals).isEmpty then
      let congr_tac ← `(tactic| simp only [
          Kernel.hom_monoComp.{$eLevelStx},
          Kernel.hom_comp.{$eLevelStx},
          Kernel.tensorHom.{$eLevelStx},
        ]
      )
      try
        evalTactic congr_tac
      catch _ =>
        pure ()
      for e in op_data do
        match e with
        | .WhiskerLeft sfinker equiv =>
          let sfinkerStx ← Term.exprToSyntax sfinker
          let equivStx ← Term.exprToSyntax equiv
          evalTactic (← `(tactic| nth_rw 1 [
            Kernel.WhiskerLeft.{$eLevelStx} (Z' := $sfinkerStx) (ez := $equivStx)]))
          try
            evalTactic congr_tac
          catch _ =>
            pure ()
        | .WhiskerRight sfinker equiv =>
          let sfinkerStx ← Term.exprToSyntax sfinker
          let equivStx ← Term.exprToSyntax equiv
          evalTactic (← `(tactic| nth_rw 1 [
            Kernel.WhiskerRight.{$eLevelStx} (Z' := $sfinkerStx) (ez := $equivStx)]))
          try
            evalTactic congr_tac
          catch _ =>
            pure ()
        | _ => pure ()
      evalTactic (← `(tactic| rwa [Kernel.hom_congr.{$eLevelStx}]))
  | _ =>
    setGoals savedGoals
    throwError "Expected exactly two goals after `constructor`"
  if !(← getGoals).isEmpty then
    setGoals savedGoals
    throwError "Failed to solve all goals while building kernel_hom equivalence proof"

  setGoals savedGoals
  instantiateMVars mvar

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
    let eLevel ← getUniverseFromEq expr
    let (kernelExpr, op_data, _, _) ← transformEquality eLevel expr transformHomToKernel
    let eqProofType ← mkEq expr kernelExpr
    let eqProof ← mkHomKernelEqProof eqProofType eLevel op_data
    match fvarId with
    | some fid => do
      let mvarId ← getMainGoal
      let hProof ← mkEqMP eqProof (mkFVar fid)
      let userName := (← fid.getDecl).userName
      let mvarId ← mvarId.assert userName kernelExpr hProof
      let mvarId ← mvarId.tryClear fid
      let (_, mvarId) ← mvarId.intro1P
      pure mvarId
    | none => do
      let mvarId ← getMainGoal
      mvarId.replaceTargetEq kernelExpr eqProof

@[inherit_doc ApplyHomKernel]
syntax (name := homKernel) "hom_kernel" (ppSpace location)? : tactic

elab_rules : tactic
  | `(tactic| hom_kernel $[$loc]?) =>
    expandOptLocation (Lean.mkOptionalNode loc) |> applyLocTactic <| ApplyHomKernel
