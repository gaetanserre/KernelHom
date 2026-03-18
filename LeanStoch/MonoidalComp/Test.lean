import LeanStoch.Tactic.Tactic
import Mathlib

open ProbabilityTheory MeasureTheory CategoryTheory MonoidalCategory

variable {W : Type w} {X : Type x} {Y : Type y} {Z : Type z}
  [MeasurableSpace W] [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  [MeasurableCoherence X Y] (κ : Kernel W X) [IsSFiniteKernel κ] (η : Kernel Y Z)
  [IsSFiniteKernel η]

#check κ ⊗≫ₖ η

example {X Y Z : Stoch} (f : 𝟙_ Stoch ⟶ X) (g : Y ⟶ Z) [MonoidalCoherence X Y] :
    (λ_ (𝟙_ Stoch)).hom ≫ f ⊗≫ g = (ρ_ (𝟙_ Stoch)).hom ≫ f ⊗≫ g := by
  coherence

def f.{u, v} {α : Type u} {β : Type v} (self : α × β) : α := Prod.fst self
def g.{u, v} {α : Type u} {β : Type v} (self : α × β) : β := Prod.snd self

example (κ : Kernel Unit X) [IsSFiniteKernel κ] (η : Kernel Y Z)
    [IsSFiniteKernel η] [MeasurableCoherence X Y] :
    κ ∘ₖ (Kernel.id.map f : Kernel (Unit × Unit) Unit) ⊗≫ₖ η = κ ∘ₖ (Kernel.id.map g) ⊗≫ₖ η := by
  kernel_coherence

variable {c c' c'' : Stoch} (f : c ⟶ c') (g : c' ⟶ c'')

example : ((f ▷ 𝟙_ Stoch) ▷ 𝟙_ Stoch) ≫ ((ρ_ c').hom ▷ 𝟙_ Stoch) ≫ ((ρ_ c').hom ≫ g)
    = ((ρ_ c).hom ▷ 𝟙_ Stoch) ≫ ((ρ_ c).hom ≫ (f ≫ g)) := by
  monoidal

example (f : Kernel X Y) (g : Kernel Y Z) [IsSFiniteKernel f] [IsSFiniteKernel g] :
    (g ∘ₖ Kernel.id.map (Prod.fst : Y × Unit → Y)) ∘ₖ
      (Kernel.id.map (Prod.fst : Y × Unit → Y) ∥ₖ Kernel.id (α := Unit)) ∘ₖ
        ((f ∥ₖ Kernel.id (α := Unit)) ∥ₖ Kernel.id (α := Unit))
    = (g ∘ₖ f ∘ₖ (Kernel.id.map (Prod.fst : X × Unit → X)) ∘ₖ
        ((Kernel.id.map (Prod.fst : X × Unit → X)) ∥ₖ Kernel.id (α := Unit))
      : Kernel ((X × Unit) × Unit) Z)
     := by
  kernel_monoidal
