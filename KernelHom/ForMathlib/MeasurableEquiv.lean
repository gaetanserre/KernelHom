/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Measurable equivalences
-/

@[expose] public section

namespace MeasurableEquiv

variable (α : Type*) [MeasurableSpace α]

/-- The identity measurable equivalence. -/
def id : α ≃ᵐ α where
  toEquiv := .refl α
  measurable_toFun := measurable_id
  measurable_invFun := measurable_id

end MeasurableEquiv
