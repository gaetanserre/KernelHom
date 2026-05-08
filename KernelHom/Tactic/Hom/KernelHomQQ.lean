/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

module

public import Lean.Elab.Tactic.Location
public import KernelHom.Kernel.MonoidalComp
public import KernelHom.Mathlib.MeasurableEquiv
public import KernelHom.Tactic.LocTactic
public import KernelHom.Tactic.Hom.Universe
public import KernelHom.Tactic.Hom.Utils

public meta section

open Lean Elab Tactic Meta Parser.Tactic

open CategoryTheory ProbabilityTheory MonoidalCategory ComonObj

open Qq MeasurableEquiv

def instantiateLevelMVarsQ (u : Level) : MetaM ((_u' : Level) ×' (u =QL _u')) := do
  return ⟨← instantiateLevelMVars u, ⟨⟩⟩

def instantiateMVarsQ' {u : Level} {α : Q(Sort u)} (e : Q($α)) :
    MetaM ((e' : Q($α)) ×' $e =Q $e') := do
  return ⟨← instantiateMVarsQ e, ⟨⟩⟩

abbrev QHom {u v : Level} {α : Q(Type u)} {β : Q(Type v)}
    (mα : Q(MeasurableSpace $α)) (mβ : Q(MeasurableSpace $β)) :=
  (_u' : Level) -- The common universe level where all types are lifted to
  × (α' : Q(SFinKer.{_u'})) -- The lifted source type
  × (β' : Q(SFinKer.{_u'})) -- The lifted target type
  × Q(($α').carrier ≃ᵐ $α) -- Measurable equivalence from the lifted source to the original
  × Q(($β').carrier ≃ᵐ $β) -- Measurable equivalence from the lifted target to the original
  × Q($α' ⟶ $β') -- The corresponding morphism in the category of S-finite kernels

partial def constructLiftedTypeQ {u : Level} (α : Q(Type u)) (maxLvl : Level) :
    MetaM (Q(Type max u maxLvl)) := do
  try
    let .defEq _ ← isLevelDefEqQ ql(u) ql(1) | throwError "Expected universe level 1, got: {u}"
    return q(PUnit.{max u maxLvl})
  catch _ =>
    try
      let .some ⟨_u, _v, α', β, _hu, _h⟩ : Option (
          (u' v : Level)
          × (α' : Q(Type u'))
          × (β : Q(Type v))
          × (_ : u =QL max u' v)
          ×' $α =Q @Prod.{u', v} $α' $β)
      ← (withNewMCtxDepth do
        let u' ← mkFreshLevelMVar
        let v ← mkFreshLevelMVar
        let α' ← mkFreshExprMVarQ q(Type u')
        let β ← mkFreshExprMVarQ q(Type v)
        let .defEq _ ← isLevelDefEqQ ql(u) ql(max u' v)
          | throwError "Mismatched universe levels: {u} and {u'.max v}"
        let .defEq _ ← isDefEqQ q($α) q($α' × $β)
          | throwError "Expected a product type, got: {α}"
        let ⟨u', _⟩ ← instantiateLevelMVarsQ u'
        let ⟨v, _⟩ ← instantiateLevelMVarsQ v
        let ⟨α', _⟩ ← instantiateMVarsQ' q($α')
        let ⟨β, _⟩ ← instantiateMVarsQ' q($β)
        return some ⟨u', v, α', β, ⟨⟩, ⟨⟩⟩
      ) | throwError "Failed to match product type: {α}"
      let lifted_α' ← constructLiftedTypeQ α' maxLvl
      let lifted_β ← constructLiftedTypeQ β maxLvl
      return q($lifted_α' × $lifted_β)
    catch _ =>
      match α with
      | ~q(PUnit) =>
        return q(PUnit.{max u maxLvl + 1})
      | _ =>
        return q(ULift.{maxLvl} (α := $α))

def transformKernelIdQ {u : Level} {α : Q(Type u)} {mα : Q(MeasurableSpace $α)}
    (κ : Q(Kernel $α $α)) (maxLvl : Level) : MetaM (QHom mα mα) := do
  match κ with
  | ~q(Kernel.id) =>
    let e := q(𝟙 SFinKer.of <| ULift.{max u maxLvl} (α := $α))
    return ⟨
      u.max maxLvl,
      q(SFinKer.of <| ULift.{max u maxLvl} (α := $α)),
      q(SFinKer.of <| ULift.{max u maxLvl} (α := $α)),
      q(ulift.{u, max u maxLvl} (α := $α)),
      q(ulift.{u, max u maxLvl} (α := $α)),
      e
    ⟩
  | _ => throwError "Expected identity kernel, got: {κ}"

/- def transformKernelCopyQ {u : Level} {α : Q(Type u)} {mα : Q(MeasurableSpace $α)}
    (κ : Q(Kernel $α ($α × $α))) (maxLvl : Level) :
    MetaM (QHom mα q(($mα).prod $mα)) := do
  match κ with
  | ~q(Kernel.copy _) =>
    let e := q(Δ[SFinKer.of <| ULift.{max u maxLvl} (α := $α)])
    return ⟨
      u.max maxLvl,
    sorry
  | _ => throwError "Expected identity kernel, got: {κ}" -/

partial def transformKernelToHomQ' {u v : Level} {α : Q(Type u)} {β : Q(Type v)}
    {mα : Q(MeasurableSpace $α)} {mβ : Q(MeasurableSpace $β)} (κ : Q(Kernel $α $β))
    (maxLvl : Level) : MetaM (QHom mα mβ) := do
  let eαt ← constructLiftedTypeQ α maxLvl
  let eβt ← constructLiftedTypeQ β maxLvl
  logInfo m!"Attempting to transform kernel {κ} to hom with lifted types {eαt} and {eβt}"
  try
    let .defEq _ ← isLevelDefEqQ ql(u) ql(v) | throwError "Mismatched universe levels: {u} and {v}"
    let .defEq _ ← isDefEqQ q($α) q($β) | throwError "Mismatched types: {α} and {β}"
    return ← transformKernelIdQ κ maxLvl
  catch _ =>
    match κ with
    | ~q($κ ∘ₖ $η) =>
      let ⟨lvl, ι, β', _, eβ', hom_κ⟩ ← transformKernelToHomQ' κ maxLvl
      let ⟨lvl', α', ι', eα', _, hom_η⟩ ← transformKernelToHomQ' η maxLvl
      let .defEq _ ← isLevelDefEqQ ql(lvl) ql(lvl')
        | throwError "Mismatched universe levels: {lvl} and {lvl'}"
      let .defEq _ ← isDefEqQ q($ι) q($ι') |
        throwError "Mismatched intermediate types: {ι} and {ι'}"
      return ⟨lvl, α', β', eα', eβ', q($hom_η ≫ $hom_κ)⟩
    | ~q(@Kernel.monoComp _ $X $Y _ _ $mX $mY _ $m_coherence $κ $mκ $η $mη) =>
      let ⟨lvl, α', ι, eα', eι, hom_κ⟩ ← transformKernelToHomQ' κ maxLvl
      let ⟨lvl', ξ, β', eξ, eβ', hom_η⟩ ← transformKernelToHomQ' η maxLvl
      let .defEq _ ← isLevelDefEqQ ql(lvl) ql(lvl')
        | throwError "Mismatched universe levels: {lvl} and {lvl'}"
      have : Q(MonoidalCoherence $ι $ξ) :=
        q(MeasurableCoherence.monoidalCoherence $eι $eξ)
      return (⟨lvl, α', β', eα', eβ', q($hom_κ ⊗≫ $hom_η)⟩ : QHom mα mβ)
    | ~q($κ) =>
      let eα : Q(ULift.{max u v maxLvl} $α ≃ᵐ $α) := q(ulift.{u, max u v maxLvl} (α := $α))
      let eβ : Q(ULift.{max u v maxLvl} $β ≃ᵐ $β):= q(ulift.{v, max u v maxLvl} (α := $β))
      have := ← synthInstanceQ (q(IsSFiniteKernel $κ))
      return (⟨
        (u.max v).max maxLvl,
        q(SFinKer.of <| ULift.{max u v maxLvl} (α := $α)),
        q(SFinKer.of <| ULift.{max u v maxLvl} (α := $β)),
        eα,
        eβ,
        q(Kernel.hom (ex := $eα) (ey := $eβ) $κ)
      ⟩ : QHom mα mβ)
    | _ =>
      throwError "No match for: {κ}"

partial def transformKernelToHomQ (maxLvl : Level) (κ : Expr) (op_data : List CategoryOP) :
    MetaM (Expr × List CategoryOP) := do
  let ⟨u, α, κ⟩ ← inferTypeQ κ
  let .some ⟨_u, _v, _α, _b, _mα, _mβ, _hu, _h⟩ :
      Option (
        (u' v' : Level) × (α' : Q(Type u')) × (β' : Q(Type v')) × (mα : Q(MeasurableSpace $α'))
        × (mβ : Q(MeasurableSpace $β'))
        × (_ : u =QL max u' v' + 1) ×' $α =Q @Kernel.{u', v'} $α' $β' $mα $mβ)
    ← (withNewMCtxDepth do
      let u' ← mkFreshLevelMVar
      let v' ← mkFreshLevelMVar
      let α' ← mkFreshExprMVarQ q(Type u')
      let β' ← mkFreshExprMVarQ q(Type v')
      let mα ← mkFreshExprMVarQ q(MeasurableSpace $α')
      let mβ ← mkFreshExprMVarQ q(MeasurableSpace $β')
      let .defEq _ ← isLevelDefEqQ ql(u) ql(max u' v' + 1) | pure none
      let .defEq _ ← isDefEqQ q($α) q(@Kernel.{u', v'} $α' $β' $mα $mβ) | pure none
      let ⟨u', _⟩ ← instantiateLevelMVarsQ u'
      let ⟨v', _⟩ ← instantiateLevelMVarsQ v'
      let ⟨α', _⟩ ← instantiateMVarsQ' q($α')
      let ⟨β', _⟩ ← instantiateMVarsQ' q($β')
      let ⟨mα, _⟩ ← instantiateMVarsQ' q($mα)
      let ⟨mβ, _⟩ ← instantiateMVarsQ' q($mβ)
      return some ⟨u', v', α', β', mα, mβ, ⟨⟩, ⟨⟩⟩) | throwError "Failed to match kernel type: {κ}"
  let ⟨_, _, _, _, _, e⟩ ← transformKernelToHomQ' q($κ) maxLvl
  logInfo m!"Transformed kernel {κ} to {e}"
  return (κ, op_data)

def ApplyKernelHomQ (goal : MVarId) (fvarId : Option FVarId) : TacticM MVarId := do
  goal.withContext do
    let expr ← match fvarId with
        | some fid => do
          let decl ← fid.getDecl
          pure decl.type
        | none => goal.getType
    let expr ← unfold_kernel_op expr
    let maxLvl ← compute_max_universe (← collectExprUniverses expr)
    let (homExpr, op_data, rhs, lhs) ← transformEquality maxLvl expr transformKernelToHomQ
    let eqProofType ← mkEq expr homExpr
    getMainGoal

@[inherit_doc ApplyKernelHomQ]
syntax (name := kernelHomQ) "kernel_homQ" (ppSpace location)? : tactic

elab_rules : tactic
  | `(tactic| kernel_homQ $[$loc]?) =>
    expandOptLocation (Lean.mkOptionalNode loc) |> applyLocTactic <| ApplyKernelHomQ
