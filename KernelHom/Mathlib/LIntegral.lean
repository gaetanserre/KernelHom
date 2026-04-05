/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

open ENNReal MeasureTheory

/-!
# Lebesgue integral utilities

This file provides helper lemmas for the Lebesgue integral with Dirac measures.

## Main declarations

- `lintegral_lintegral_dirac`: computing nested integrals with Dirac measures.
-/

lemma lintegral_lintegral_dirac {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {f : β → ℝ≥0∞} {g : α → β}
    (hf : Measurable f) : ∫⁻ a, ∫⁻ b, f b ∂(Measure.dirac (g a)) ∂μ = ∫⁻ a, f (g a) ∂μ := by
  simp_rw [lintegral_dirac' _ hf]
