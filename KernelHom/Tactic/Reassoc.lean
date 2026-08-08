/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Tactic.CategoryTheory.Reassoc
public import KernelHom.Tactic.HomKernel

/-!
-/

public meta section

open Lean Meta Elab Tactic ProbabilityTheory

namespace Mathlib.Tactic.Reassoc

def HomEqualityToLvl (eq : Expr) (Lvl : Level) : MetaM (Expr × Expr) := do
  let eq ← unfoldKernelOp eq
  let (lifted_expr, lifted_proof) ← liftEqualityWithLevel Lvl eq
  let some (_, lhs, rhs) := lifted_expr.eq? | throwError "Expected an equality, got: {lifted_expr}."
  let (lhs_hom, proofs) ← transformKernelToHom lhs []
  let (rhs_hom, proofs) ← transformKernelToHom rhs proofs
  let hom_expr ← mkEq lhs_hom rhs_hom
  let hom_eq_proof_type ← mkEq lifted_expr hom_expr
  let hom_eq_proof ← mkKernelHomEqProof hom_eq_proof_type lhs rhs proofs
  return (hom_expr, ← mkEqTrans lifted_proof hom_eq_proof)

def freshenLevelParam (e : Expr) : MetaM Expr := do
  let mvarIds := (Lean.collectLevelMVars {} e).result
  for mvarId in mvarIds do
    Lean.assignLevelMVar mvarId (Level.param mvarId.name)
  instantiateMVars e

def kernelReassocHandler (h_eq : Expr) : MetaM (Expr × Array MVarId) := do
  let eq_type ← inferType h_eq
  let some (_, lhs, _) := eq_type.eq? |
    throwError "Expected an equality, but got {eq_type}"
  let (_, Y, _, yLvl) ← getTypesFromKernel lhs
  let proof : Expr ←
    withLocalDecl `Z .implicit (mkSort (mkLevelSucc yLvl)) fun Z => do
      let mspaceType ← mkAppM ``MeasurableSpace #[Z]
      withLocalDecl `inst .instImplicit mspaceType fun _inst => do
        let kernelType ← mkAppMInst ``Kernel #[Y, Z] 2
        withLocalDeclD `ξ kernelType fun ξ => do
          let sfiniteType ← mkAppM ``IsSFiniteKernel #[ξ]
          withLocalDecl `inst_1 BinderInfo.instImplicit sfiniteType fun _inst_1 => do
            let (_, hom_proof) ← HomEquality eq_type
            let hom_proof ← mkAppM ``Eq.mp #[hom_proof, h_eq]
            let (hom_proof_reassoc, _) ← reassocExprHom hom_proof
            let maxLvl ← computeMaxLevel <| ← collectExprUniverses eq_type
            let (ξ_lift, _) ← liftKernel ξ maxLvl []
            let (ξ_hom, _) ← transformKernelToHom ξ_lift []
            let reassoc_body ← mkAppM' hom_proof_reassoc #[ξ_hom]
            let (_, kernel_reassoc_proof) ← KernelEquality <| ← inferType reassoc_body
            let test ← mkAppM ``Eq.mp #[kernel_reassoc_proof, reassoc_body]
            mkLambdaFVars #[Z, _inst, ξ, _inst_1] test
  return (proof, #[])

initialize registerReassocExpr kernelReassocHandler

open Lean Elab Tactic Meta in
elab "test_handler " t:term : tactic => do
  let e ← elabTerm t none
  let (e', _) ← kernelReassocHandler e
  logInfo m!"résultat: {e'}"

end Mathlib.Tactic.Reassoc
