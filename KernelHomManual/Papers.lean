/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import VersoManual
open Verso.Genre.Manual

def fritz2020 : InProceedings where
  title := inlines!"A synthetic approach to Markov kernels, conditional independence and theorems
  on sufficient statistics"
  authors := #[inlines!"Tobias Fritz"]
  year := 2020
  booktitle := inlines!"Advances in Mathematics"

def douc2018 : InProceedings where
  title := inlines!"Markov Chains"
  authors := #[inlines!"Randal Douc", inlines!"Eric Moulines", inlines!"Pierre Priouret",
    inlines!"Philippe Soulier"]
  year := 2018
  booktitle := inlines!"Springer Series in Operations Research and Financial Engineering"
