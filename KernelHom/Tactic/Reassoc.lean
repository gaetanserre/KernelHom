/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Tactic.CategoryTheory.Reassoc
public import KernelHom.Tactic.KernelHom

/-!
-/

public meta section

open Lean Meta Elab Tactic

namespace Mathlib.Tactic.Reassoc

def dummyGoal : MetaM MVarId := do
  return (← mkFreshExprMVar (mkConst ``True)).mvarId!

def runTacticMInMetaM (goal : MVarId) (tac : TacticM Expr) : MetaM Expr := do
  let (some e, _) ← (Tactic.run_for goal tac).run'
    | throwError "la tactique n'a pas produit de résultat"
  instantiateMVars e

def runTacticMInMetaM' (goal : MVarId) (tac : TacticM α) : MetaM α := do
  let ctx : Tactic.Context := { elaborator := .anonymous, recover := false }
  goal.withContext do
    let (a, _) ← ((tac.run ctx).run { goals := [goal] }).run' {} {}
    pure a

def kernelReassocHandler (e : Expr) : MetaM (Expr × Array MVarId) := do
  logInfo m!"kernelReassocHandler: {e}"
  let mvar ← dummyGoal
  let t ← runTacticMInMetaM' mvar (HomEquality (← inferType e) >>= fun x => pure x.1)
  logInfo m!"kernelReassocHandler: {t}"
  return (e, #[])

initialize registerReassocExpr kernelReassocHandler

open Lean Elab Tactic Meta in
elab "test_handler " t:term : tactic => do
  let e ← elabTerm t none
  let (e', insts) ← Mathlib.Tactic.Reassoc.kernelReassocHandler e
  logInfo m!"résultat: {e'}"

end Mathlib.Tactic.Reassoc
