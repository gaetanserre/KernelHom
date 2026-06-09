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

instance : ToMessageData CategoryOP where
  toMessageData
    | .Comp ex SX ey SY ez SZ =>
      m!"Composition with ex: {ex}, SX: {SX}, ey: {ey}, SY: {SY}, ez: {ez}, SZ: {SZ}"
    | .ParallelComp ex SX ey SY ez SZ et ST =>
      m!"Parallel composition with ex: {ex}, SX: {SX}, ey: {ey}, SY: {SY}, ez: {ez},
      SZ: {SZ}, et: {et}, ST: {ST}"
    | .Id ex SX => m!"Identity with ex: {ex}, SX: {SX}"

/-- Unfold kernel operations in an expression. -/
def unfoldKernelOp (e : Expr) : MetaM Expr := do
  let names := (.empty |> NameSet.insert <| ``Kernel.prod) |> NameSet.insert <| ``Kernel.compProd
  transform e (post := fun e => do
    let e' ← deltaExpand e names.contains
    let e' ← Core.betaReduce e'
    return .done e')
