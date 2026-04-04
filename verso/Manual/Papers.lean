/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoManual
open Verso.Genre.Manual

def legall2016 : InProceedings where
  title := inlines!"Brownian motion, martingales, and stochastic calculus"
  -- Add a weird unicode space character to avoid the name being split
  authors := #[inlines!"Jean-François Le Gall"]
  year := 2016
  booktitle := inlines!"Springer"
