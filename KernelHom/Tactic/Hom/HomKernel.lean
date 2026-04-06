/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import KernelHom.Tactic.Hom.KernelHom

/-!
# `hom_kernel` tactic

This file implements the `hom_kernel` tactic, the inverse of `kernel_hom`.
It transforms equalities written in the monoidal category back into
equivalent equalities of kernels.

## Main declarations

- `transformHomToKernel`: recursive translation from categorical morphism expressions to
  kernel expressions.
- `mkHomKernelEqProof`: construction of the equivalence proof used by the
  tactic.
- `applyHomKernel`: core implementation on goals and hypotheses.
- `hom_kernel`: user-facing tactic (with location support).
-/

open Lean Elab Tactic Meta CategoryTheory Parser.Tactic ProbabilityTheory MonoidalCategory

/-- Get the original type and its universe from a `SFinKer.of` expression. -/
partial def get_type_from_SFinKer (e : Expr) : MetaM (Expr × Level) := do
  let ewhnf ← whnf e
  match ewhnf.getAppFn with
  | Expr.const ``PUnit _ | Expr.const ``Unit _ =>
    return (Expr.const ``Unit [], Level.zero)
  | Expr.const ``Prod _ =>
    let args := ewhnf.getAppArgs
    let X := args[0]!
    let Y := args[1]!
    let (ex, xLevel) ← get_type_from_SFinKer X
    let (ey, yLevel) ← get_type_from_SFinKer Y
    let res ← mkAppOptM' (Expr.const ``Prod [xLevel, yLevel]) #[ex, ey]
    return (res, Level.max xLevel yLevel)
  | Expr.const ``ULift _ =>
    let args := ewhnf.getAppArgs
    let X := args[0]!
    return ← get_type_from_SFinKer X
  | Expr.const ``MonoidalCategoryStruct.tensorUnit _ =>
    return (Expr.const ``Unit [], Level.zero)
  | Expr.const ``SFinKer.of _ =>
    let args := ewhnf.getAppArgs
    if args.size < 1 then
      throwError "SFinKer.of with insufficient arguments: {e}"
    else
      return ← get_type_from_SFinKer args[0]!
  | _ =>
    match ← getLevel e with
    | Level.succ l => return (e, l)
    | _ => throwError "Expected a type with a universe level ≥ 0, got: {e}"

/-- Deconstruct a left or right unitor morphism to get the underlying kernel -/
def deconstruct_unitors_hom (iso : Expr) (eLevel : Level) (left : Bool) :
    MetaM (Expr × CategoryOP) := do
  let iso_t ← inferType iso
  let (X, xLevel) ← get_type_from_SFinKer iso_t.getAppArgs[3]!
  let kernel_id ←
    if left then
      let UnitX ← mkAppOptM' (Expr.const ``Prod [Level.zero, xLevel]) #[Expr.const ``Unit [], X]
      let mUnitX ← synthInstance (mkApp (Expr.const ``MeasurableSpace [xLevel]) UnitX)
      mkAppOptM ``Kernel.id #[UnitX, mUnitX]
    else
      let XUnit ← mkAppOptM' (Expr.const ``Prod [xLevel, Level.zero]) #[X, Expr.const ``Unit []]
      let mXUnit ← synthInstance (mkApp (Expr.const ``MeasurableSpace [xLevel]) XUnit)
      mkAppOptM ``Kernel.id #[XUnit, mXUnit]
  let prod ← if left then
      mkAppOptM ``Prod.snd #[Expr.const ``Unit [], X]
    else
      mkAppOptM ``Prod.fst #[X, Expr.const ``Unit []]
  let ex ← construct_measurable_equiv X xLevel eLevel
  let OP := if left then .leftUnitor_hom xLevel ex else .rightUnitor_hom xLevel ex
  return (← mkAppM ``Kernel.map #[kernel_id, prod], OP)

/-- Deconstruct a left or right unitor inverse morphism to get the underlying kernel -/
def deconstruct_unitors_inv (iso : Expr) (eLevel : Level) (left : Bool) :
    MetaM (Expr × CategoryOP) := do
  let iso_t ← inferType iso
  let (X, xLevel) ← get_type_from_SFinKer iso_t.getAppArgs[3]!
  let kernel_id ← do
    let mX ← synthInstance (mkApp (Expr.const ``MeasurableSpace [xLevel]) X)
    mkAppOptM ``Kernel.id #[X, mX]
  let f :=
    if left then
      Expr.lam `x X (
        (((.const ``Prod.mk [Level.zero, xLevel] |> Expr.app <| .const ``Unit [])
        |> Expr.app <| X) |> Expr.app <| .const ``Unit.unit []) |> Expr.app <| .bvar 0
      ) .default
    else
      Expr.lam `x X (
        (((.const ``Prod.mk [xLevel, Level.zero] |> Expr.app <| X) |> Expr.app
        <| .const ``Unit []) |> Expr.app <| .bvar 0) |> Expr.app <| .const ``Unit.unit []
      ) .default
  let ex ← construct_measurable_equiv X xLevel eLevel
  let OP := if left then .leftUnitor_inv xLevel ex else .rightUnitor_inv xLevel ex
  return (← mkAppM ``Kernel.map #[kernel_id, f], OP)

/-- Deconstruct a left or right whisker to get the underlying kernel and the whiskered object -/
def deconstruct_whiskers_hom_args (e : Expr) (eLevel : Level) (left : Bool) :
    MetaM (Expr × Expr × CategoryOP) := do
  let args := e.getAppArgs
  let SX := if left then args[args.size - 4]! else args[args.size - 1]!
  let κ := if left then args[args.size - 1]! else args[args.size - 2]!
  let (X, xLevel) ← get_type_from_SFinKer SX
  let mXUnit ← synthInstance (mkApp (Expr.const ``MeasurableSpace [xLevel]) X)
  let kernel_id ← mkAppOptM ``Kernel.id #[X, mXUnit]
  let exEquiv ← construct_measurable_equiv X xLevel eLevel
  let OP := if left then .WhiskerLeft exEquiv else .WhiskerRight exEquiv
  return (κ, kernel_id, OP)

/-- Deconstruct the associator morphism to get the underlying kernel -/
def deconstruct_associator_hom (iso : Expr) (eLevel : Level) : MetaM (Expr × CategoryOP) := do
  let args := iso.getAppArgs
  let (X, xLevel) ← get_type_from_SFinKer args[args.size - 3]!
  let (Y, yLevel) ← get_type_from_SFinKer args[args.size - 2]!
  let (Z, zLevel) ← get_type_from_SFinKer args[args.size - 1]!
  let XY ← mkAppOptM ``Prod #[X, Y]
  let XYZ ← mkAppOptM ``Prod #[XY, Z]
  let mXYZ ← synthInstance (mkApp
    (Expr.const ``MeasurableSpace [Level.max (Level.max xLevel yLevel) zLevel]) XYZ)
  let kernel_id ← mkAppOptM ``Kernel.id #[XYZ, mXYZ]
  let YZ ← mkAppOptM ``Prod #[Y, Z]
  let p := .bvar 0
  let p1 := ((.const ``Prod.fst [Level.max xLevel yLevel, zLevel] |> Expr.app <| XY)
    |> Expr.app <| Z) |> Expr.app <| p
  let p2 := ((.const ``Prod.snd [Level.max xLevel yLevel, zLevel] |> Expr.app <| XY)
    |> Expr.app <| Z) |> Expr.app <| p
  let p11 := ((.const ``Prod.fst [xLevel, yLevel] |> Expr.app <| X)
    |> Expr.app <| Y) |> Expr.app <| p1
  let p12 := ((.const ``Prod.snd [xLevel, yLevel] |> Expr.app <| X)
    |> Expr.app <| Y) |> Expr.app <| p1
  let innerProd :=
    .app
      (.app
        (.app
          (.app (.const ``Prod.mk [yLevel, zLevel]) Y)
          Z)
        p12)
      p2
  let body :=
    .app
      (.app
        (.app
          (.app (.const ``Prod.mk [xLevel, Level.max yLevel zLevel]) X)
          YZ)
        p11)
      innerProd
  let assoc_fn := Expr.lam `p XYZ body .default
  let res ← mkAppM ``Kernel.map #[kernel_id, assoc_fn]
  let ex ← construct_measurable_equiv X xLevel eLevel
  let ey ← construct_measurable_equiv Y yLevel eLevel
  let ez ← construct_measurable_equiv Z zLevel eLevel
  let OP := .Associator_hom ex ey ez
  return (res, OP)

/-- Deconstruct the associator inverse morphism to get the underlying kernel -/
def deconstruct_associator_inv (iso : Expr) (eLevel : Level) : MetaM (Expr × CategoryOP) := do
  let args := iso.getAppArgs
  let (X, xLevel) ← get_type_from_SFinKer args[args.size - 3]!
  let (Y, yLevel) ← get_type_from_SFinKer args[args.size - 2]!
  let (Z, zLevel) ← get_type_from_SFinKer args[args.size - 1]!
  let YZ ← mkAppOptM ``Prod #[Y, Z]
  let XYZ ← mkAppOptM ``Prod #[X, YZ]
  let mXYZ ← synthInstance (mkApp
    (Expr.const ``MeasurableSpace [Level.max xLevel (Level.max yLevel zLevel)]) XYZ)
  let kernel_id ← mkAppOptM ``Kernel.id #[XYZ, mXYZ]
  let XY ← mkAppOptM ``Prod #[X, Y]
  let p := .bvar 0
  let p1 := ((.const ``Prod.fst [xLevel, Level.max yLevel zLevel] |> Expr.app <| X)
    |> Expr.app <| YZ) |> Expr.app <| p
  let p2 := ((.const ``Prod.snd [xLevel, Level.max yLevel zLevel] |> Expr.app <| X)
    |> Expr.app <| YZ) |> Expr.app <| p
  let p21 := ((.const ``Prod.fst [yLevel, zLevel] |> Expr.app <| Y)
    |> Expr.app <| Z) |> Expr.app <| p2
  let p22 := ((.const ``Prod.snd [yLevel, zLevel] |> Expr.app <| Y)
    |> Expr.app <| Z) |> Expr.app <| p2
  let innerProd :=
    .app
      (.app
        (.app
          (.app (.const ``Prod.mk [xLevel, yLevel]) X)
          Y)
        p1)
      p21
  let body :=
    .app
      (.app
        (.app
          (.app (.const ``Prod.mk [Level.max xLevel yLevel, zLevel]) XY)
          Z)
        innerProd)
      p22
  let assoc_fn := Expr.lam `p XYZ body .default
  let res ← mkAppM ``Kernel.map #[kernel_id, assoc_fn]
  let ex ← construct_measurable_equiv X xLevel eLevel
  let ey ← construct_measurable_equiv Y yLevel eLevel
  let ez ← construct_measurable_equiv Z zLevel eLevel
  let OP := .Associator_inv ex ey ez
  return (res, OP)

/-- Recursive transformation from morphism expression in `SFinKer` to kernel expression. -/
-- ANCHOR: transformHomToKernel
partial def transformHomToKernel (eLevel : Level) (e : Expr) (op_data : List CategoryOP) :
    MetaM (Expr × List CategoryOP) := do
  match e.getAppFn with
  | Expr.const ``CategoryStruct.id _ =>
    let args := e.getAppArgs
    let X := args[args.size - 1]!
    let (X', xLevel) ← get_type_from_SFinKer X
    let ex ← construct_measurable_equiv X' xLevel eLevel
    let mX' ← synthInstance (mkApp (Expr.const ``MeasurableSpace [xLevel]) X')
    return (← mkAppOptM ``Kernel.id #[X', mX'], .id ex :: op_data)
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
    | Expr.const ``MonoidalCategoryStruct.leftUnitor _ =>
      let (res, leftUnitorOP) ← deconstruct_unitors_hom iso eLevel true
      return (res, leftUnitorOP :: op_data)
    | Expr.const ``MonoidalCategoryStruct.rightUnitor _ =>
      let (res, rightUnitorOP) ← deconstruct_unitors_hom iso eLevel false
      return (res, rightUnitorOP :: op_data)
    | Expr.const ``MonoidalCategoryStruct.associator _ =>
      let (res, associatorHomOP) ← deconstruct_associator_hom iso eLevel
      return (res, associatorHomOP :: op_data)
    | Expr.const ``BraidedCategory.braiding _ =>
      let args := iso.getAppArgs
      let (X, xLevel) ← get_type_from_SFinKer args[args.size - 2]!
      let (Y, yLevel) ← get_type_from_SFinKer args[args.size -1]!
      let ex ← construct_measurable_equiv X xLevel eLevel
      let ey ← construct_measurable_equiv Y yLevel eLevel
      let e ← mkAppOptM ``Kernel.swap #[X, Y, none, none]
      return (e, .Braiding_hom ex ey :: op_data)
    | _ => throwError "Unexpected isomorphism {iso}"
  | Expr.const ``Iso.inv _ =>
    let args := e.getAppArgs
    let iso := args[args.size - 1]!
    match iso.getAppFn with
    | Expr.const ``MonoidalCategoryStruct.associator _ =>
      let (res, associatorInvOP) ← deconstruct_associator_inv iso eLevel
      return (res, associatorInvOP :: op_data)
    | Expr.const ``MonoidalCategoryStruct.leftUnitor _ =>
      let (res, leftUnitorInvOP) ← deconstruct_unitors_inv iso eLevel true
      return (res, leftUnitorInvOP :: op_data)
    | Expr.const ``MonoidalCategoryStruct.rightUnitor _ =>
      let (res, rightUnitorInvOP) ← deconstruct_unitors_inv iso eLevel false
      return (res, rightUnitorInvOP :: op_data)
    | _ => throwError "Expected a monoidal isomorphism, got: {iso}"
  | Expr.const ``MonoidalCategoryStruct.whiskerLeft _ =>
    let (κ, kernel_id, whiskerLeftOP) ← deconstruct_whiskers_hom_args e eLevel true
    let (κ', lκ) ← transformHomToKernel eLevel κ op_data
    let res ← mkAppM ``Kernel.parallelComp #[kernel_id, κ']
    return (res, whiskerLeftOP :: lκ)
  | Expr.const ``MonoidalCategoryStruct.whiskerRight _ =>
    let (κ, kernel_id, whiskerRightOP) ← deconstruct_whiskers_hom_args e eLevel false
    let (κ', lκ) ← transformHomToKernel eLevel κ op_data
    return (← mkAppM ``Kernel.parallelComp #[κ', kernel_id], whiskerRightOP :: lκ)
  | Expr.const ``MonoidalCategoryStruct.tensorHom _ =>
    let args := e.getAppArgs
    let κ := args[args.size - 2]!
    let η := args[args.size - 1]!
    let (κ', lκ) ← transformHomToKernel eLevel κ op_data
    let (η', lη) ← transformHomToKernel eLevel η lκ
    return (← mkAppM ``Kernel.parallelComp #[κ', η'], lη)
  | Expr.const ``ComonObj.counit _ =>
    let args := e.getAppArgs
    let (X, xLevel) ← get_type_from_SFinKer args[args.size - 2]!
    let ex ← construct_measurable_equiv X xLevel eLevel
    let discard_kernel_const := Expr.const ``Kernel.discard [xLevel, Level.zero]
    return (← mkAppOptM' discard_kernel_const #[X, none], .Counit ex :: op_data)
  | Expr.const ``ComonObj.comul _ =>
    let args := e.getAppArgs
    let (X, xLevel) ← get_type_from_SFinKer args[args.size - 2]!
    let ex ← construct_measurable_equiv X xLevel eLevel
    return (← mkAppOptM ``Kernel.copy #[X, none], .Comul ex :: op_data)
  | Expr.const ``Kernel.hom _ =>
    let args := e.getAppArgs
    let κ := args[args.size - 2]!
    return (κ, op_data)
  | _ => throwError "Expected a hom expression, got: {e}"
-- ANCHOR_END: transformHomToKernel

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
    evalTactic (← `(tactic| try dsimp only [MonoidalCategoryStruct.tensorUnit,
      MonoidalCategoryStruct.tensorObj] at h))
    for e in op_data do
      match e with
      | .leftUnitor_hom _ expr =>
        let eStx ← Term.exprToSyntax expr
        evalTactic (← `(tactic| try rw [Kernel.leftUnitor_hom.{_, _, 0} (ex := $eStx)] at h))
      | .leftUnitor_inv _ expr =>
        let eStx ← Term.exprToSyntax expr
        evalTactic (← `(tactic| try rw [Kernel.leftUnitor_inv.{_, _, 0} (ex := $eStx)] at h))
      | .rightUnitor_hom _ expr =>
        let eStx ← Term.exprToSyntax expr
        evalTactic (← `(tactic| try rw [Kernel.rightUnitor_hom.{_, _, 0} (ex := $eStx)] at h))
      | .rightUnitor_inv _ expr =>
        let eStx ← Term.exprToSyntax expr
        evalTactic (← `(tactic| try rw [Kernel.rightUnitor_inv.{_, _, 0} (ex := $eStx)] at h))
      | .id equiv =>
        let eStx ← Term.exprToSyntax equiv
        evalTactic (← `(tactic| try rw [Kernel.hom_id (ex := $eStx)] at h))
      | .Associator_hom ex ey ez =>
        let exStx ← Term.exprToSyntax ex
        let eyStx ← Term.exprToSyntax ey
        let ezStx ← Term.exprToSyntax ez
        evalTactic (← `(tactic| try rw [Kernel.associator_hom (ex := $exStx) (ey := $eyStx)
          (ez := $ezStx)] at h))
      | .Associator_inv ex ey ez =>
        let exStx ← Term.exprToSyntax ex
        let eyStx ← Term.exprToSyntax ey
        let ezStx ← Term.exprToSyntax ez
        evalTactic (← `(tactic| try rw [Kernel.associator_inv (ex := $exStx) (ey := $eyStx)
          (ez := $ezStx)] at h))
      | .Braiding_hom ex ey =>
        let exStx ← Term.exprToSyntax ex
        let eyStx ← Term.exprToSyntax ey
        evalTactic (← `(tactic| try rw [Kernel.braiding_hom (ex := $exStx) (ey := $eyStx)] at h))
      | .Counit equiv =>
        let eStx ← Term.exprToSyntax equiv
        evalTactic (← `(tactic| try rw [Kernel.counit (ex := $eStx)] at h))
      | .Comul equiv =>
        let eStx ← Term.exprToSyntax equiv
        evalTactic (← `(tactic| try rw [Kernel.comul (ex := $eStx)] at h))
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
        | .WhiskerLeft equiv =>
          let eStx ← Term.exprToSyntax equiv
          evalTactic (← `(tactic| rw [Kernel.WhiskerLeft.{$eLevelStx} (ez := $eStx)] at h))
        | .WhiskerRight equiv =>
          let eStx ← Term.exprToSyntax equiv
          evalTactic (← `(tactic| rw [Kernel.WhiskerRight.{$eLevelStx} (ez := $eStx)] at h))
        | _ => pure ()
      try
        evalTactic congr_tac
      catch _ =>
        pure ()

      evalTactic (← `(tactic| rwa [Kernel.quiver_congr.{$eLevelStx}] at h))

    setGoals [backwardGoal]
    evalTactic (← `(tactic| intro h))
    evalTactic (← `(tactic| try dsimp only [MonoidalCategoryStruct.tensorUnit,
      MonoidalCategoryStruct.tensorObj]))
    for e in op_data do
      match e with
      | .leftUnitor_hom _ expr =>
        let eStx ← Term.exprToSyntax expr
        evalTactic (← `(tactic| try rw [Kernel.leftUnitor_hom.{_, _, 0} (ex := $eStx)]))
      | .leftUnitor_inv _ expr =>
        let eStx ← Term.exprToSyntax expr
        evalTactic (← `(tactic| try rw [Kernel.leftUnitor_inv.{_, _, 0} (ex := $eStx)]))
      | .rightUnitor_hom _ expr =>
        let eStx ← Term.exprToSyntax expr
        evalTactic (← `(tactic| try rw [Kernel.rightUnitor_hom.{_, _, 0} (ex := $eStx)]))
      | .rightUnitor_inv _ expr =>
        let eStx ← Term.exprToSyntax expr
        evalTactic (← `(tactic| try rw [Kernel.rightUnitor_inv.{_, _, 0} (ex := $eStx)]))
      | .id equiv =>
        let eStx ← Term.exprToSyntax equiv
        evalTactic (← `(tactic| try rw [Kernel.hom_id (ex := $eStx)]))
      | .Associator_hom ex ey ez =>
        let exStx ← Term.exprToSyntax ex
        let eyStx ← Term.exprToSyntax ey
        let ezStx ← Term.exprToSyntax ez
        evalTactic (← `(tactic| try rw [Kernel.associator_hom (ex := $exStx) (ey := $eyStx)
          (ez := $ezStx)]))
      | .Associator_inv ex ey ez =>
        let exStx ← Term.exprToSyntax ex
        let eyStx ← Term.exprToSyntax ey
        let ezStx ← Term.exprToSyntax ez
        evalTactic (← `(tactic| try rw [Kernel.associator_inv (ex := $exStx) (ey := $eyStx)
          (ez := $ezStx)]))
      | .Braiding_hom ex ey =>
        let exStx ← Term.exprToSyntax ex
        let eyStx ← Term.exprToSyntax ey
        evalTactic (← `(tactic| try rw [Kernel.braiding_hom (ex := $exStx) (ey := $eyStx)]))
      | .Counit equiv =>
        let eStx ← Term.exprToSyntax equiv
        evalTactic (← `(tactic| try rw [Kernel.counit (ex := $eStx)]))
      | .Comul equiv =>
        let eStx ← Term.exprToSyntax equiv
        evalTactic (← `(tactic| try rw [Kernel.comul (ex := $eStx)]))
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
        | .WhiskerLeft equiv =>
          let eStx ← Term.exprToSyntax equiv
          evalTactic (← `(tactic| rw [Kernel.WhiskerLeft.{$eLevelStx} (ez := $eStx)]))
        | .WhiskerRight equiv =>
          let eStx ← Term.exprToSyntax equiv
          evalTactic (← `(tactic| rw [Kernel.WhiskerRight.{$eLevelStx} (ez := $eStx)]))
        | _ => pure ()
      try
        evalTactic congr_tac
      catch _ =>
        pure ()
      evalTactic (← `(tactic| rwa [Kernel.quiver_congr.{$eLevelStx}]))
  | _ =>
    setGoals savedGoals
    throwError "Expected exactly two goals after `constructor`"
  if !(← getGoals).isEmpty then
    setGoals savedGoals
    throwError "Failed to solve all goals while building kernel_hom equivalence proof"

  setGoals savedGoals
  instantiateMVars mvar

/-- Core implementation of the `hom_kernel` tactic on a single goal or hypothesis. -/
def applyHomKernel (goal : MVarId) (fvarId : Option FVarId) : TacticM MVarId := do
  goal.withContext do
    let expr ← match fvarId with
        | some fid => do
          let decl ← fid.getDecl
          pure decl.type
        | none => goal.getType
    let eLevel ← get_universe_from_eq expr
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
syntax "hom_kernel" (ppSpace location)? : tactic

-- ANCHOR: hom_kernel_tactic
elab_rules : tactic
  | `(tactic| hom_kernel $[$loc]?) =>
    expandOptLocation (Lean.mkOptionalNode loc) |> applyLocTactic <| applyHomKernel
-- ANCHOR_END: hom_kernel_tactic

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

-- ANCHOR: example_hom_kernel
example (κ η : Kernel X Y) [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (h : κ = η) : κ ∘ₖ Kernel.id = η := by
  kernel_hom
  simp only [Category.id_comp]
  hom_kernel
  exact h
-- ANCHOR_END: example_hom_kernel
