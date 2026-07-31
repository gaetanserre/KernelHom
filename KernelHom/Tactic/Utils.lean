/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import KernelLift.ForMathlib.MeasurableEquiv
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Kernel.Composition.CompProd

/-!
# Kernel transformation utilities
-/

public meta section

open Lean Meta ProbabilityTheory

inductive CategoryOP
  | Comp (ex SX ey SY ez SZ : Expr)
  | ParallelComp (ex SX ey SY ez SZ et ST : Expr)
  | Id (ex SX : Expr)
  | Discard (ex SX : Expr)
  | Copy (ex SX : Expr)
  | WhiskerLeft (ex SX : Expr)
  | WhiskerRight (ex SX : Expr)
  | LeftUnitor (ex SX ex₀ : Expr) (UnitLvl : Level)
  | RightUnitor (ex SX ex₀ : Expr) (UnitLvl : Level)

instance : ToMessageData CategoryOP where
  toMessageData
    | .Comp ex SX ey SY ez SZ =>
      m!"Composition with ex: {ex}, SX: {SX}, ey: {ey}, SY: {SY}, ez: {ez}, SZ: {SZ}"
    | .ParallelComp ex SX ey SY ez SZ et ST =>
      m!"Parallel composition with ex: {ex}, SX: {SX}, ey: {ey}, SY: {SY}, ez: {ez},
      SZ: {SZ}, et: {et}, ST: {ST}"
    | .Id ex SX => m!"Identity with ex: {ex}, SX: {SX}"
    | .Discard ex SX => m!"Discard with ex: {ex}, SX: {SX}"
    | .Copy ex SX => m!"Copy with ex: {ex}, SX: {SX}"
    | .WhiskerLeft ex SX => m!"Whisker left with ex: {ex}, SX: {SX}"
    | .WhiskerRight ex SX => m!"Whisker right with ex: {ex}, SX: {SX}"
    | .LeftUnitor ex SX UnitLvl ex₀ => m!"Left unitor with ex: {ex}, SX: {SX}, ex₀: {ex₀},
      UnitLvl: {UnitLvl}"
    | .RightUnitor ex SX ex₀ UnitLvl => m!"Right unitor with ex: {ex}, SX: {SX}, ex₀: {ex₀},
      UnitLvl: {UnitLvl}"

/-- Unfold kernel operations in an expression. -/
def unfoldKernelOp (e : Expr) : MetaM Expr := do
  let names := (.empty |> NameSet.insert <| ``Kernel.prod) |> NameSet.insert <| ``Kernel.compProd
  transform e (post := fun e => do
    let e' ← deltaExpand e names.contains
    let e' ← Core.betaReduce e'
    return .done e')
