/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib

public meta section

open Lean Meta Elab Tactic

namespace Mathlib.Tactic.Reassoc

def kernelReassocHandler (e : Expr) : MetaM (Expr × Array MVarId) := do
  logInfo m!"kernelReassocHandler: {e}"
  return (e, #[])

initialize registerReassocExpr kernelReassocHandler

end Mathlib.Tactic.Reassoc
