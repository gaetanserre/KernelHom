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

example :
    ((f ▷ 𝟙_ Stoch) ▷ 𝟙_ Stoch) ≫ ((ρ_ c').hom ▷ 𝟙_ Stoch) ≫ ((ρ_ c').hom ≫ g)
    = ((ρ_ c).hom ▷ 𝟙_ Stoch) ≫ ((ρ_ c).hom ≫ (f ≫ g)) := by
  monoidal

open MeasurableEquiv

example (f : Kernel X Y) (g : Kernel Y Z) [IsSFiniteKernel f] [IsSFiniteKernel g] :
    (g ∘ₖ Kernel.id.map (Prod.fst : Y × PUnit.{u_1 + 1} → Y)) ∘ₖ (Kernel.id.map (Prod.fst : Y × PUnit.{u_2 + 1} → Y) ∥ₖ Kernel.id (α := PUnit)) = (0 : Kernel ((Y × PUnit) × PUnit) Z) := by
  kernel_quiver
  --dsimp [MonoidalCategoryStruct.tensorUnit]
  rw [Kernel.rightUnitor.{max y z u_1 u_2, _, u_1} (ex := ulift)]
  sorry
