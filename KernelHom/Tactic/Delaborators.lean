/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import KernelHom.Kernel.Hom
import Lean

/-!
# Delaborators for simplified kernel presentations

This file implements delaborators that provide simplified pretty-printing kernel-related
categorical operations that are generated using the `kernel_hom` tactic.
-/

open Lean Meta Elab Command PrettyPrinter Delaborator
open Lean.PrettyPrinter.Delaborator.SubExpr

namespace KernelHom.Delaborators

@[app_delab ULift]
meta def delabULift : Delab := do
  let x ← withNaryArg 0 delab
  `($x)

@[app_delab SFinKer.of]
meta def delabSFinKerOf : Delab := do
  let x ← withNaryArg 0 delab
  `($x)

@[app_delab ProbabilityTheory.Kernel.hom]
meta def delabKernelHom : Delab := do
  let x ← withNaryArg 10 delab
  `($x)

end KernelHom.Delaborators
