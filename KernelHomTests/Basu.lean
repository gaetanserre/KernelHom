/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import KernelHom

/-!
# Basu's theorem for Markov kernels

This file formalizes Theorem 15.8 of [T. Fritz, *A synthetic approach to Markov kernels, conditional
independence and theorems on sufficient statistics*](https://arxiv.org/pdf/1908.07021) for Markov
kernels. It is the main ingredient of the classical Basu theorem: a complete sufficient statistic
is independent of any ancillary statistic, for every value of the parameter. Together with Example
15.4 of the paper, which identifies completeness with bounded completeness, it essentially gives
the classical theorem (Remark 15.9 of the paper).

A statistical model is a Markov kernel `p : Kernel Θ X`. Almost sure equality, sufficiency,
completeness and ancillarity are defined as in the paper, by equalities of kernels.

The proof follows the string diagram computations of the paper: each computation step is an
equality of kernels proved with Kernel-Hom, and the hypotheses are used by rewriting.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory CategoryTheory MonoidalCategory ComonObj

open scoped KernelHom

namespace ProbabilityTheory.Kernel

variable {Θ X V W : Type*} [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace V]
  [MeasurableSpace W]

/-- The kernels `f` and `g` are `p`-almost surely equal (Definition 13.1). -/
def AEEq {Y : Type*} [MeasurableSpace Y] (p : Kernel Θ X) (f g : Kernel X Y) : Prop :=
  (f ∥ₖ Kernel.id) ∘ₖ copy X ∘ₖ p = (g ∥ₖ Kernel.id) ∘ₖ copy X ∘ₖ p

/-- The statistic `s` is sufficient for the statistical model `p` (Definition 14.3). -/
def IsSufficient (p : Kernel Θ X) (s : Kernel X V) : Prop :=
  ∃ α : Kernel V X, IsMarkovKernel α ∧
    (Kernel.id ∥ₖ s) ∘ₖ copy X ∘ₖ p = (α ∥ₖ Kernel.id) ∘ₖ copy V ∘ₖ s ∘ₖ p

/-- The kernel `f` is complete with respect to kernels with values in `Z` (Definition 15.1, which
quantifies over all `Z`). -/
def IsComplete (f : Kernel Θ X) (Z : Type*) [MeasurableSpace Z] : Prop :=
  ∀ (g h : Kernel X Z) [IsMarkovKernel g] [IsMarkovKernel h], g ∘ₖ f = h ∘ₖ f → AEEq f g h

/-- The statistic `a` is ancillary for the statistical model `p` (Definition 15.7). -/
def IsAncillary (p : Kernel Θ X) (a : Kernel X W) : Prop :=
  ∃ ψ : Kernel Unit W, IsMarkovKernel ψ ∧ a ∘ₖ p = ψ ∘ₖ discard Θ

section

variable {p : Kernel Θ X} {s : Kernel X V} {a : Kernel X W} {α : Kernel V X} {ψ : Kernel Unit W}
  [IsMarkovKernel p] [IsMarkovKernel s] [IsMarkovKernel a] [IsMarkovKernel α] [IsMarkovKernel ψ]

/-- The kernels `a ∘ₖ α` and `ψ ∘ₖ discard V` agree after `s ∘ₖ p`, where `α` witnesses the
sufficiency of `s` and `ψ` the ancillarity of `a` (first computation of the proof of
Theorem 15.8). -/
lemma basu_aux
    (hα : (Kernel.id ∥ₖ s) ∘ₖ copy X ∘ₖ p = (α ∥ₖ Kernel.id) ∘ₖ copy V ∘ₖ s ∘ₖ p)
    (hψ : a ∘ₖ p = ψ ∘ₖ discard Θ) :
    (a ∘ₖ α) ∘ₖ (s ∘ₖ p) = (ψ ∘ₖ discard V) ∘ₖ (s ∘ₖ p) := by
  calc (a ∘ₖ α) ∘ₖ (s ∘ₖ p)
  _ = Kernel.id.map Prod.fst ∘ₖ (a ∥ₖ (discard V : Kernel V Unit)) ∘ₖ
      ((α ∥ₖ Kernel.id) ∘ₖ copy V ∘ₖ s ∘ₖ p) := by
    kernel_disch
  _ = a ∘ₖ p := by
    rw [← hα]
    kernel_disch
  _ = (ψ ∘ₖ discard V) ∘ₖ (s ∘ₖ p) := by
    rw [hψ]
    kernel_disch

end

/-- **Theorem 15.8** of Fritz: if `s` is a sufficient statistic such that `s ∘ₖ p` is complete, and
`a` is ancillary, then for every value of the parameter, the joint distribution of `s` and `a` is
the product of their distributions. The kernel `a` does not need to be deterministic. -/
theorem basu {p : Kernel Θ X} [IsMarkovKernel p] {s : Kernel X V} [IsMarkovKernel s]
    {a : Kernel X W} [IsMarkovKernel a] (hs : IsSufficient p s) (hc : IsComplete (s ∘ₖ p) W)
    (ha : IsAncillary p a) : (s ∥ₖ a) ∘ₖ copy X ∘ₖ p = (s ∘ₖ p) ×ₖ (a ∘ₖ p) := by
  with_panel_widgets [KernelDiagram]
  obtain ⟨α, _, hα⟩ := hs
  obtain ⟨ψ, _, hψ⟩ := ha
  calc (s ∥ₖ a) ∘ₖ copy X ∘ₖ p
  _ = swap W V ∘ₖ ((a ∥ₖ Kernel.id) ∘ₖ ((Kernel.id ∥ₖ s) ∘ₖ copy X ∘ₖ p)) := by
    kernel_disch
  _ = swap W V ∘ₖ (a ∥ₖ Kernel.id ∘ₖ (α ∥ₖ Kernel.id ∘ₖ copy V ∘ₖ s ∘ₖ p)) := by
    rw [hα]
  _ = swap W V ∘ₖ (((a ∘ₖ α) ∥ₖ Kernel.id) ∘ₖ copy V ∘ₖ (s ∘ₖ p)) := by
    kernel_disch
  _ = swap W V ∘ₖ (((ψ ∘ₖ discard V) ∥ₖ Kernel.id) ∘ₖ copy V ∘ₖ (s ∘ₖ p)) := by
    rw [hc (a ∘ₖ α) (ψ ∘ₖ discard V) (basu_aux hα hψ)]
  _ = (s ∘ₖ p) ×ₖ (ψ ∘ₖ discard Θ) := by
    kernel_disch
  _ = (s ∘ₖ p) ×ₖ (a ∘ₖ p) := by
    rw [hψ]

section Steps

/-! ### Computation steps

Each step is an equality of the computations of `basu_aux` and `basu`, so that its string diagrams
can be drawn. -/

variable {p : Kernel Θ X} {s : Kernel X V} {a : Kernel X W} {α : Kernel V X} {ψ : Kernel Unit W}
  [IsMarkovKernel p] [IsMarkovKernel s] [IsMarkovKernel a] [IsMarkovKernel α] [IsMarkovKernel ψ]

-- The instances are needed to draw the string diagrams of a step, even when its proof does not use
-- them.
set_option linter.unusedSectionVars false

lemma basu_aux_step₁ :
    (a ∘ₖ α) ∘ₖ (s ∘ₖ p) =
      Kernel.id.map Prod.fst ∘ₖ (a ∥ₖ (discard V : Kernel V Unit)) ∘ₖ
        ((α ∥ₖ Kernel.id) ∘ₖ copy V ∘ₖ s ∘ₖ p) := by
  kernel_disch

/-- By sufficiency. -/
lemma basu_aux_step₂
    (hα : (Kernel.id ∥ₖ s) ∘ₖ copy X ∘ₖ p = (α ∥ₖ Kernel.id) ∘ₖ copy V ∘ₖ s ∘ₖ p) :
    Kernel.id.map Prod.fst ∘ₖ (a ∥ₖ (discard V : Kernel V Unit)) ∘ₖ
        ((α ∥ₖ Kernel.id) ∘ₖ copy V ∘ₖ s ∘ₖ p) = a ∘ₖ p := by
  rw [← hα]
  kernel_disch

/-- By ancillarity. -/
lemma basu_aux_step₃ (hψ : a ∘ₖ p = ψ ∘ₖ discard Θ) :
    a ∘ₖ p = (ψ ∘ₖ discard V) ∘ₖ (s ∘ₖ p) := by
  rw [hψ]
  kernel_disch

lemma basu_step₁ :
    (s ∥ₖ a) ∘ₖ copy X ∘ₖ p =
      swap W V ∘ₖ ((a ∥ₖ Kernel.id) ∘ₖ ((Kernel.id ∥ₖ s) ∘ₖ copy X ∘ₖ p)) := by
  kernel_disch

/-- By sufficiency. -/
lemma basu_step₂
    (hα : (Kernel.id ∥ₖ s) ∘ₖ copy X ∘ₖ p = (α ∥ₖ Kernel.id) ∘ₖ copy V ∘ₖ s ∘ₖ p) :
    swap W V ∘ₖ ((a ∥ₖ Kernel.id) ∘ₖ ((Kernel.id ∥ₖ s) ∘ₖ copy X ∘ₖ p)) =
      swap W V ∘ₖ (a ∥ₖ Kernel.id ∘ₖ (α ∥ₖ Kernel.id ∘ₖ copy V ∘ₖ s ∘ₖ p)) := by
  rw [hα]

lemma basu_step₃ :
    swap W V ∘ₖ (a ∥ₖ Kernel.id ∘ₖ (α ∥ₖ Kernel.id ∘ₖ copy V ∘ₖ s ∘ₖ p)) =
      swap W V ∘ₖ (((a ∘ₖ α) ∥ₖ Kernel.id) ∘ₖ copy V ∘ₖ (s ∘ₖ p)) := by
  kernel_disch

/-- By completeness, with `basu_aux`. -/
lemma basu_step₄ (h : AEEq (s ∘ₖ p) (a ∘ₖ α) (ψ ∘ₖ discard V)) :
    swap W V ∘ₖ (((a ∘ₖ α) ∥ₖ Kernel.id) ∘ₖ copy V ∘ₖ (s ∘ₖ p)) =
      swap W V ∘ₖ (((ψ ∘ₖ discard V) ∥ₖ Kernel.id) ∘ₖ copy V ∘ₖ (s ∘ₖ p)) := by
  rw [h]

lemma basu_step₅ :
    swap W V ∘ₖ (((ψ ∘ₖ discard V) ∥ₖ Kernel.id) ∘ₖ copy V ∘ₖ (s ∘ₖ p)) =
      (s ∘ₖ p) ×ₖ (ψ ∘ₖ discard Θ) := by
  kernel_disch

/-- By ancillarity. -/
lemma basu_step₆ (hψ : a ∘ₖ p = ψ ∘ₖ discard Θ) :
    (s ∘ₖ p) ×ₖ (ψ ∘ₖ discard Θ) = (s ∘ₖ p) ×ₖ (a ∘ₖ p) := by
  rw [hψ]

end Steps

end ProbabilityTheory.Kernel
