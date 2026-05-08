import KernelHom.Tactic.Tactics

open ProbabilityTheory CategoryTheory MonoidalCategory

variable {T X Y Z : Type*} [MeasurableSpace T] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]

variable {κ : Kernel X Y} {ξ : Kernel Z T} {η : Kernel Y Z} [IsSFiniteKernel κ]
  [IsSFiniteKernel ξ] [IsSFiniteKernel η] [MeasurableCoherence Y Z]

example : Kernel.id = (0 : Kernel X X) := by
  kernel_homQ
  sorry
