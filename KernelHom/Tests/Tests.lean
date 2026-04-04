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

example (κ : Kernel X Y) (η : Kernel Y Z) (ξ : Kernel Z W)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] [IsFiniteKernel ξ]
    (h : ξ ∘ₖ (η ∘ₖ κ) = ξ ∘ₖ η ∘ₖ κ) :
    ξ ∘ₖ (η ∘ₖ κ) = ξ ∘ₖ η ∘ₖ κ := by
  kernel_hom at h
  hom_kernel at h
  exact h

example (h : Kernel.id.map (Prod.snd : Unit × X → X) = (0 : Kernel (Unit × X) X)) :
    Kernel.id.map (Prod.snd : Unit × X → X) = (0 : Kernel (Unit × X) X) := by
  kernel_hom at h
  hom_kernel at h
  exact h

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
