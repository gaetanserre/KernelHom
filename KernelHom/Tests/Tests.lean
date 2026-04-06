/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import KernelHom.Tactic.Tactics

open ProbabilityTheory MeasureTheory CategoryTheory MonoidalCategory

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

example (κ : Kernel W Z) [IsSFiniteKernel κ] :
    (Kernel.id (α := X × Y)) ∥ₖ κ =
    ((Kernel.id.map fun p ↦ ((p.1, p.2.1), p.2.2)) ∘ₖ (Kernel.id ∥ₖ (Kernel.id ∥ₖ κ)) ∘ₖ
      Kernel.id.map fun p ↦ (p.1.1, p.1.2, p.2)) := by
  kernel_hom
  simp only [tensor_whiskerLeft]
  hom_kernel
  rfl

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
