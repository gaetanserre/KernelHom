/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import KernelHom

/-!
# Tests for Kernel-Hom
-/

@[expose] public section

open ProbabilityTheory MeasureTheory CategoryTheory MonoidalCategory KernelHom

/-! Tests for `kernel_hom` and `hom_kernel`. -/

variable {W X Y Z : Type*}
  [MeasurableSpace W] [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

example (κ : Kernel X Y) (η : Kernel Y Z) (ξ : Kernel Z W)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] [IsFiniteKernel ξ] :
    ξ ∘ₖ (η ∘ₖ κ) = ξ ∘ₖ η ∘ₖ κ := by
  kernel_hom
  simp only [Category.assoc]

example (h : Kernel.id.map (Prod.snd : Unit × X → X) = (0 : Kernel (Unit × X) X)) :
    Kernel.id.map (Prod.snd : Unit × X → X) = (0 : Kernel (Unit × X) X) := by
  kernel_hom at h
  hom_kernel at h
  exact h

example (κ : Kernel W Z) [IsSFiniteKernel κ] :
    (Kernel.id (α := Unit)) ∥ₖ κ = (0 : Kernel (Unit × W) (Unit × Z)) := by
  kernel_hom
  simp only [id_whiskerLeft]
  hom_kernel
  sorry

example (κ : Kernel W Z) [IsSFiniteKernel κ] :
    (κ ∥ₖ Kernel.id (α := Unit)) = (0 : Kernel (W × Unit) (Z × Unit)) := by
  kernel_hom
  simp only [whiskerRight_id]
  hom_kernel
  sorry

open MeasurableEquiv in
example (κ : Kernel W Z) [IsSFiniteKernel κ] :
    (Kernel.id (α := X × Y)) ∥ₖ κ =
    ((Kernel.deterministic prodAssoc.symm (by fun_prop)) ∘ₖ (Kernel.id ∥ₖ (Kernel.id ∥ₖ κ)) ∘ₖ
      Kernel.deterministic prodAssoc (by fun_prop)) := by
  kernel_monoidal

example (κ : Kernel X Y) (η : Kernel Y Z) (ξ : Kernel Z W)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] [IsFiniteKernel ξ] :
    ξ ∥ₖ κ = 0 := by
  kernel_hom
  hom_kernel
  sorry

example (κ : Kernel X Y) (η : Kernel Y Z) [IsFiniteKernel η] [IsSFiniteKernel κ]
    (h : (Kernel.id (α := Unit)) ∥ₖ (η ∘ₖ κ) =
      (0 : Kernel (Unit × X) (Unit × Z))) :
    (Kernel.id (α := Unit)) ∥ₖ (η ∘ₖ κ) = (0 : Kernel (Unit × X) (Unit × Z)) := by
  kernel_hom at h
  hom_kernel at h
  exact h

example (f : Kernel X Y) (g : Kernel Y Z) [IsSFiniteKernel f] [IsSFiniteKernel g] :
    (g ∘ₖ Kernel.id.map (Prod.fst : Y × PUnit → Y)) ∘ₖ
      (Kernel.id.map (Prod.fst : Y × PUnit → Y) ∥ₖ Kernel.id (α := PUnit)) ∘ₖ
        ((f ∥ₖ Kernel.id (α := PUnit)) ∥ₖ Kernel.id (α := PUnit))
    = (g ∘ₖ f ∘ₖ (Kernel.id.map (Prod.fst : X × PUnit → X)) ∘ₖ
        ((Kernel.id.map (Prod.fst : X × PUnit → X)) ∥ₖ Kernel.id (α := PUnit))
      : Kernel ((X × PUnit) × PUnit) Z)
     := by
  kernel_monoidal

example (κ η : Kernel X Y) [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (h : κ = η) : κ ∘ₖ Kernel.id = η := by
  kernel_hom
  simp only [Category.id_comp]
  hom_kernel
  exact h

open scoped ComonObj in
example (κ : Kernel Z Y) [IsSFiniteKernel κ] :
    (Kernel.discard.{_, 0} Z ∥ₖ κ) ∘ₖ Kernel.copy Z = (Kernel.id.map fun x ↦ ((), x)) ∘ₖ κ := by
  kernel_hom
  simp only [ComonObj.counit_comul_hom]
  hom_kernel
  rfl

example (κ : Kernel Y Z) [IsSFiniteKernel κ] (f : X → Y) (hf : Measurable f) :
    Kernel.swap Z Z ∘ₖ Kernel.copy Z ∘ₖ κ ∘ₖ Kernel.deterministic f hf =
      Kernel.copy Z ∘ₖ κ.comap f hf := by
  kernel_hom
  simp only [IsCommComonObj.comul_comm]
  hom_kernel
  rw [Kernel.comp_assoc, Kernel.comp_deterministic_eq_comap]

example (κ : Kernel X Y) (η : Kernel Z W) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    Kernel.swap Y W ∘ₖ (κ ∥ₖ η) = η ∥ₖ κ ∘ₖ Kernel.swap X Z := by
  aesop_kernel

example (κ : Kernel X Y) (η : Kernel Y Z) (ζ : Kernel X Z) (ξ : Kernel Z W) [IsSFiniteKernel κ]
    [IsSFiniteKernel η] [IsSFiniteKernel ζ] [IsSFiniteKernel ξ] (h : η ∘ₖ κ = ζ) :
    ξ ∘ₖ η ∘ₖ κ = ξ ∘ₖ ζ := by
  kernel_hom at h ⊢
  rw [reassoc_of% h]

example (κ : Kernel X Y) (η : Kernel Z W) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    (Kernel.id ∥ₖ κ) ∘ₖ (η ∥ₖ Kernel.id) = (η ∥ₖ Kernel.id) ∘ₖ (Kernel.id ∥ₖ κ) := by
  kernel_disch

example (p : Kernel X Y) (s : Kernel Y Z) (ψ : Kernel Unit W) [IsMarkovKernel p]
    [IsMarkovKernel s] [IsDeterministic s] [IsMarkovKernel ψ] :
    ψ ∘ₖ Kernel.discard X = (ψ ∘ₖ Kernel.discard Z) ∘ₖ (s ∘ₖ p) := by
  kernel_disch

/-! Tests for `Kernel.compProd`, which is an `irreducible_def` and is unfolded by rewriting. -/

example (κ : Kernel X Y) (η : Kernel (X × Y) Z) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    κ ⊗ₖ η = Kernel.swap Z Y ∘ₖ (η ∥ₖ Kernel.id)
      ∘ₖ Kernel.deterministic MeasurableEquiv.prodAssoc.symm (by fun_prop)
      ∘ₖ (Kernel.id ∥ₖ Kernel.copy Y) ∘ₖ (Kernel.id ∥ₖ κ) ∘ₖ Kernel.copy X := by
  kernel_monoidal

example (κ : Kernel X Y) (η : Kernel (X × Y) Z) [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (h : κ ⊗ₖ η = 0) : κ ⊗ₖ η = 0 := by
  kernel_hom at h ⊢
  exact h

example (κ : Kernel X Y) (η : Kernel (X × Y) Z) (f : Kernel Y W) (g : Kernel Z W)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] [IsSFiniteKernel f] [IsSFiniteKernel g] :
    (f ∥ₖ g) ∘ₖ (κ ⊗ₖ η) = (f ∥ₖ Kernel.id) ∘ₖ (Kernel.id ∥ₖ g) ∘ₖ (κ ⊗ₖ η) := by
  kernel_disch

example (κ : Kernel X Y) (η : Kernel (X × Y) Z) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    κ ⊗ₖ η = Kernel.swap Z Y ∘ₖ (η ∥ₖ Kernel.id)
      ∘ₖ Kernel.deterministic MeasurableEquiv.prodAssoc.symm (by fun_prop)
      ∘ₖ (Kernel.id ∥ₖ Kernel.copy Y) ∘ₖ (Kernel.id ∥ₖ κ) ∘ₖ Kernel.copy X := by
  set ζ := κ ⊗ₖ η
  kernel_monoidal

/-! `@[kernel_reassoc]` and `kernel_reassoc_of%` on equalities stated with `⊗ₖ`. Unfolding
`Kernel.compProd` adds universe levels (through the coercion of `MeasurableEquiv.prodAssoc.symm`),
and the kernel `ξ` of the generated lemma must be lifted to the same level as the equality. -/

@[kernel_reassoc]
lemma compProd_eq_of_eq (κ : Kernel X Y) (η : Kernel (X × Y) Z) (ζ : Kernel X (Y × Z))
    [IsSFiniteKernel κ] [IsSFiniteKernel η] [IsSFiniteKernel ζ] (h : κ ⊗ₖ η = ζ) :
    κ ⊗ₖ η = ζ := h

example (κ : Kernel X Y) (η : Kernel (X × Y) Z) (ζ : Kernel X (Y × Z)) (ξ : Kernel (Y × Z) W)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] [IsSFiniteKernel ζ] [IsSFiniteKernel ξ]
    (h : κ ⊗ₖ η = ζ) : ξ ∘ₖ (κ ⊗ₖ η) = ξ ∘ₖ ζ := by
  have h' := compProd_eq_of_eq_assoc κ η ζ h ξ
  guard_hyp h' : ξ ∘ₖ (κ ⊗ₖ η) = ξ ∘ₖ ζ
  have h'' := (kernel_reassoc_of% h) ξ
  guard_hyp h'' : ξ ∘ₖ (κ ⊗ₖ η) = ξ ∘ₖ ζ
  exact h'

/-! `hom_kernel` folds back the products `×ₖ` and composition-products `⊗ₖ` that `kernel_hom`
unfolds, so that the lemmas generated by `@[kernel_reassoc]` rewrite goals stated with them. -/

example (κ : Kernel X Y) (η : Kernel X Z) (ζ : Kernel X (Y × Z))
    [IsSFiniteKernel κ] [IsSFiniteKernel η] [IsSFiniteKernel ζ] (h : κ ×ₖ η = ζ) :
    κ ×ₖ η = ζ := by
  kernel_hom at h ⊢
  hom_kernel at h ⊢
  guard_hyp h : κ ×ₖ η = ζ
  guard_target = κ ×ₖ η = ζ
  exact h

example (κ : Kernel X Y) (η : Kernel (X × Y) Z) (ζ : Kernel X (Y × Z))
    [IsSFiniteKernel κ] [IsSFiniteKernel η] [IsSFiniteKernel ζ] (h : κ ⊗ₖ η = ζ) :
    κ ⊗ₖ η = ζ := by
  kernel_hom at h ⊢
  hom_kernel at h ⊢
  guard_hyp h : κ ⊗ₖ η = ζ
  guard_target = κ ⊗ₖ η = ζ
  exact h

@[kernel_reassoc]
lemma prod_eq_of_eq (κ : Kernel X Y) (η : Kernel X Z) (ζ : Kernel X (Y × Z))
    [IsSFiniteKernel κ] [IsSFiniteKernel η] [IsSFiniteKernel ζ] (h : κ ×ₖ η = ζ) :
    κ ×ₖ η = ζ := h

example (κ : Kernel X Y) (η : Kernel X Z) (ζ : Kernel X (Y × Z)) (ξ : Kernel (Y × Z) W)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] [IsSFiniteKernel ζ] [IsSFiniteKernel ξ]
    (h : κ ×ₖ η = ζ) (ρ : Kernel W Y) [IsSFiniteKernel ρ] :
    ρ ∘ₖ ξ ∘ₖ (κ ×ₖ η) = ρ ∘ₖ ξ ∘ₖ ζ := by
  have h' := prod_eq_of_eq_assoc κ η ζ h ξ
  guard_hyp h' : ξ ∘ₖ (κ ×ₖ η) = ξ ∘ₖ ζ
  rw [prod_eq_of_eq_assoc κ η ζ h]

@[kernel_reassoc]
lemma prod_comp_eq_of_eq (κ : Kernel X Y) (η : Kernel X Z) (ζ : Kernel W X)
    (ρ : Kernel W (Y × Z)) [IsSFiniteKernel κ] [IsSFiniteKernel η] [IsSFiniteKernel ζ]
    [IsSFiniteKernel ρ] (h : (κ ×ₖ η) ∘ₖ ζ = ρ) : (κ ×ₖ η) ∘ₖ ζ = ρ := h

example (κ : Kernel X Y) (η : Kernel X Z) (ζ : Kernel W X) (ρ : Kernel W (Y × Z))
    (ξ : Kernel (Y × Z) W) [IsSFiniteKernel κ] [IsSFiniteKernel η] [IsSFiniteKernel ζ]
    [IsSFiniteKernel ρ] [IsSFiniteKernel ξ] (h : (κ ×ₖ η) ∘ₖ ζ = ρ) :
    ξ ∘ₖ (κ ×ₖ η) ∘ₖ ζ = ξ ∘ₖ ρ := by
  have h' := prod_comp_eq_of_eq_assoc κ η ζ ρ h ξ
  guard_hyp h' : ξ ∘ₖ (κ ×ₖ η) ∘ₖ ζ = ξ ∘ₖ ρ
  rw [prod_comp_eq_of_eq_assoc κ η ζ ρ h]

@[kernel_reassoc]
lemma prod_parallelComp_eq_of_eq (κ : Kernel X Y) (η : Kernel X Z) (θ : Kernel W W)
    (ρ : Kernel (X × W) ((Y × Z) × W)) [IsSFiniteKernel κ] [IsSFiniteKernel η]
    [IsSFiniteKernel θ] [IsSFiniteKernel ρ] (h : (κ ×ₖ η) ∥ₖ θ = ρ) : (κ ×ₖ η) ∥ₖ θ = ρ := h

example (κ : Kernel X Y) (η : Kernel X Z) (θ : Kernel W W) (ρ : Kernel (X × W) ((Y × Z) × W))
    (ξ : Kernel ((Y × Z) × W) W) [IsSFiniteKernel κ] [IsSFiniteKernel η] [IsSFiniteKernel θ]
    [IsSFiniteKernel ρ] [IsSFiniteKernel ξ] (h : (κ ×ₖ η) ∥ₖ θ = ρ) :
    ξ ∘ₖ ((κ ×ₖ η) ∥ₖ θ) = ξ ∘ₖ ρ := by
  have h' := prod_parallelComp_eq_of_eq_assoc κ η θ ρ h ξ
  guard_hyp h' : ξ ∘ₖ ((κ ×ₖ η) ∥ₖ θ) = ξ ∘ₖ ρ
  rw [prod_parallelComp_eq_of_eq_assoc κ η θ ρ h]

/-- A composition-product rewritten inside a longer composition. -/
example (κ : Kernel X Y) (η : Kernel (X × Y) Z) (ζ : Kernel X (Y × Z)) (ξ : Kernel (Y × Z) W)
    (ρ : Kernel W Y) [IsSFiniteKernel κ] [IsSFiniteKernel η] [IsSFiniteKernel ζ]
    [IsSFiniteKernel ξ] [IsSFiniteKernel ρ] (h : κ ⊗ₖ η = ζ) :
    ρ ∘ₖ ξ ∘ₖ (κ ⊗ₖ η) = ρ ∘ₖ ξ ∘ₖ ζ := by
  rw [compProd_eq_of_eq_assoc κ η ζ h]
