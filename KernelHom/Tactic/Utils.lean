/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import EqLift.Tactic.Kernel.Utils
public import KernelHom.ForMathlib.Kernel
public import KernelHom.Kernel.Hom
public meta import Qq

/-!
# Kernel transformation utilities

Utilities for the `kernel_hom` and `hom_kernel` tactics, built with `Qq`.

## Main declarations

* `unfoldKernelOp`, `foldKernelOp`: unfold and fold back `Kernel.prod` and `Kernel.compProd`.
* `kernelLevel`: the universe level of a lifted kernel.
* `homCarrier`: the object of `SFinKer` associated with a measurable space.
* `liftCarrier`: the same, for the lifted source of a measurable equivalence `X ≃ᵐ X₀`.
* `typeOfObj`: the carrier of an object of `SFinKer`.
* `objLevel`: the universe level of an object of `SFinKer`.
-/

public meta section

open Lean Meta Qq ProbabilityTheory CategoryTheory MonoidalCategory

/-- Unfold kernel operations in an expression. Returns the unfolded expression `e'` together with a
proof of `e = e'`. `Kernel.prod` is delta-expanded, while `Kernel.compProd`, being an
`irreducible_def`, is rewritten using `Kernel.compProd_def`. -/
def unfoldKernelOp (e : Expr) : MetaM (Expr × Expr) := do
  let e ← zetaReduce (← instantiateMVars e)
  let e ← transform e (post := fun e => do
    return .done (← Core.betaReduce (← deltaExpand e (· == ``Kernel.prod))))
  if !e.containsConst (· == ``Kernel.compProd) then
    return (e, ← mkEqRefl e)
  let thms ← ({} : SimpTheorems).addConst ``Kernel.compProd_def
  let ctx ← Simp.mkContext (config := { dsimp := false }) (simpTheorems := #[thms])
    (congrTheorems := ← getSimpCongrTheorems)
  let (r, _) ← simp e ctx
  return (r.expr, ← r.getProof)

/-- Fold back `Kernel.compProd` and `Kernel.prod` in an expression, in the form produced by
`unfoldKernelOp` and possibly reassociated. Returns the folded expression `e'` together with a proof
of `e = e'`. As the compositions associate to the left, an operation preceded by a kernel `ξ` is not
a subterm of its unfolding, `ξ ∘ₖ (κ ∥ₖ η) ∘ₖ copy α` for a product: each operation is folded by two
lemmas, with and without such a prefix. `Kernel.compProd` is folded first, since its unfolding
contains the unfolding `(Kernel.id ∥ₖ κ) ∘ₖ copy α` of a product. -/
def foldKernelOp (e : Expr) : MetaM (Expr × Expr) := do
  let e ← instantiateMVars e
  if !e.containsConst (· == ``Kernel.copy) then
    return (e, ← mkEqRefl e)
  let pass (e : Expr) (lemmas : List (Name × Bool)) : MetaM (Expr × Expr) := do
    let mut thms : SimpTheorems := {}
    for (name, inv) in lemmas do
      thms ← thms.addConst name (inv := inv)
    let ctx ← Simp.mkContext (config := { dsimp := false }) (simpTheorems := #[thms])
      (congrTheorems := ← getSimpCongrTheorems)
    let (r, _) ← simp e ctx
    -- A fold by `parallelComp_comp_copy`, which holds by `rfl`, is definitional: `simp` gives
    -- no proof, and `Eq.refl` of the folded term would be dropped by `mkEqTrans`, so that the
    -- final proof would have the unfolded form in its type. `hom_kernel` uses the returned
    -- expression and the kernel accepts the mismatch by unfolding `Kernel.prod`, but
    -- `@[kernel_reassoc]` reads its statement from the type of the proof. The proof is
    -- therefore `Eq.refl e` with the explicit type `e = r.expr`.
    match r.proof? with
    | some p => return (r.expr, p)
    | none => return (r.expr, ← mkExpectedTypeHint (← mkEqRefl e) (← mkEq e r.expr))
  let (e, p₁) ← pass e [(``Kernel.comp_compProd_def_eq_comp_compProd, false),
    (``Kernel.compProd_def, true)]
  let (e, p₂) ← pass e [(``Kernel.comp_parallelComp_comp_copy_eq_comp_prod, false),
    (``Kernel.parallelComp_comp_copy, false)]
  return (e, ← mkEqTrans p₁ p₂)

/-- `synthInstanceQ` with the memoization of `synthInstanceCached`. -/
def synthInstanceQCached {u : Level} (α : Q(Sort u)) : MetaM Q($α) :=
  synthInstanceCached α

/-- Simplify the maxima `max l l` of a level, which appear in the universe levels of the products
of types living in the same universe `Type l`. -/
def dedupMaxLevel : Level → Level
  | .max a b =>
    let a := dedupMaxLevel a
    let b := dedupMaxLevel b
    if a == b then a else mkLevelMax a b
  | l => l

/-- The universe level `u` of the carriers of a lifted kernel `κ : Kernel X Y`: all the carriers of
a lifted equality live in `Type u`, and the translation takes place in `SFinKer.{u}`. -/
def kernelLevel (κ : Expr) : MetaM Level := do
  let (_, _, xLvl, _) ← getTypesFromKernel κ
  return dedupMaxLevel xLvl

/-- The object `SX` of `SFinKer.{u}` associated with a measurable space `X : Type u`, together with
the `MeasurableSpace` instance of `X` and the measurable equivalence `SX ≃ᵐ X`. Products are
decomposed into tensor products and `PUnit` into the monoidal unit, so that the monoidal tactics see
the tensor structure (memoized). -/
partial def homCarrier (u : Level) (X : Expr) : MetaM
    ((X : Q(Type u)) × (_ : Q(MeasurableSpace $X)) × (SX : Q(SFinKer.{u})) × Q($SX ≃ᵐ $X)) := do
  have X : Q(Type u) := X
  let res ← memoized `homCarrier X do
    match_expr X with
    | Prod A B =>
      let ⟨A, mA, SA, eA⟩ ← homCarrier u A
      let ⟨B, mB, SB, eB⟩ ← homCarrier u B
      return #[q(@Prod.instMeasurableSpace $A $B $mA $mB), q($SA ⊗ $SB),
        q(MeasurableEquiv.prodCongr $eA $eB)]
    | PUnit => return #[(q(PUnit.instMeasurableSpace) : Q(MeasurableSpace PUnit.{u + 1})),
        q(𝟙_ SFinKer.{u}), q(MeasurableEquiv.punit.{u, u})]
    | _ =>
      let mX ← synthInstanceQCached q(MeasurableSpace $X)
      return #[mX, q(SFinKer.of $X), q(MeasurableEquiv.refl $X)]
  return ⟨X, res[0]!, res[1]!, res[2]!⟩

/-- For a measurable equivalence `e₀ : X ≃ᵐ X₀` from a lifted measurable space `X : Type u` to the
original space `X₀ : Type v` (an equivalence of `Kernel.lift`, or a component of one): the data of
`homCarrier` for `X`, then `X₀` with its universe level and its `MeasurableSpace` instance, and
`e₀`. -/
def liftCarrier (u : Level) (e₀ : Expr) :
    MetaM ((X : Q(Type u)) × (_ : Q(MeasurableSpace $X)) × (SX : Q(SFinKer.{u})) ×
      (_ : Q($SX ≃ᵐ $X)) × (v : Level) × (X₀ : Q(Type v)) × (_ : Q(MeasurableSpace $X₀)) ×
      Q($X ≃ᵐ $X₀)) := do
  let_expr MeasurableEquiv X X₀ _ mX₀ := ← inferType e₀
    | throwError "Expected a measurable equivalence, got: {e₀}."
  let ⟨X, mX, SX, ex⟩ ← homCarrier u X
  return ⟨X, mX, SX, ex, ← getDecLevel X₀, X₀, mX₀, e₀⟩

/-- The carrier of an object of `SFinKer.{u}` built from `SFinKer.of`, `⊗` and `𝟙_`, decomposed
into products and `PUnit` as in `homCarrier`. -/
partial def typeOfObj (u : Level) (SX : Expr) : MetaM Q(Type u) := do
  match_expr SX with
  | SFinKer.of X _ => return X
  | MonoidalCategoryStruct.tensorObj _ _ _ SA SB =>
    let A ← typeOfObj u SA
    let B ← typeOfObj u SB
    return q($A × $B)
  | MonoidalCategoryStruct.tensorUnit _ _ _ => return q(PUnit.{u + 1})
  | _ => throwError "Expected an object built from `SFinKer.of`, `⊗` and `𝟙_`, got: {SX}."

/-- The universe level `u` of an object of `SFinKer.{u}`. -/
def objLevel (SX : Expr) : MetaM Level := do
  match (← inferType SX).getAppFn with
    | .const ``SFinKer [u] => return u
    | _ => throwError "Expected an object of SFinKer, got: {SX}."

end
