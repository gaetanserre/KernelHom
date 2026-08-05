import KernelHom.Tactic.Reassoc

open ProbabilityTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (κ η : Kernel X Y) (h : κ = η)

include h in
@[reassoc]
lemma test : κ = η := h

#check test_assoc
