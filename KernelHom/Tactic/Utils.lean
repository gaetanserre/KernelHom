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

/-- Transport data of `SFinKer` morphisms and operations resulting from kernel "morphization". -/
inductive CategoryOP
  | Comp (ex SX ey SY ez SZ : Expr)
  | ParallelComp (ex SX ey SY ez SZ et ST : Expr)
  | Id (ex SX : Expr)
  | Discard (ex SX : Expr)
  | Copy (ex SX : Expr)
  | WhiskerLeft (ex SX : Expr)
  | WhiskerRight (ex SX : Expr)
  | LeftUnitorHom (ex SX ex₀ : Expr)
  | LeftUnitorInv (ex SX ex₀ : Expr)
  | RightUnitorHom (ex SX ex₀ : Expr)
  | RightUnitorInv (ex SX ex₀ : Expr)
  | AssociatorHom (ex SX ey SY ez SZ ex₀ ey₀ ez₀ : Expr)
  | AssociatorInv (ex SX ey SY ez SZ ex₀ ey₀ ez₀ : Expr)
  | BraidingHom (ex SX ey SY : Expr)

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
    | .LeftUnitorHom ex SX ex₀ => m!"Left unitor hom with ex: {ex}, SX: {SX}, ex₀: {ex₀}"
    | .LeftUnitorInv ex SX ex₀ => m!"Left unitor inv with ex: {ex}, SX: {SX}, ex₀: {ex₀}"
    | .RightUnitorHom ex SX ex₀ => m!"Right unitor hom with ex: {ex}, SX: {SX}, ex₀: {ex₀}"
    | .RightUnitorInv ex SX ex₀ => m!"Right unitor inv with ex: {ex}, SX: {SX}, ex₀: {ex₀}"
    | .AssociatorHom ex SX ey SY ez SZ ex₀ ey₀ ez₀ =>
      m!"Associator hom with ex: {ex}, SX: {SX}, ey: {ey}, SY: {SY}, ez: {ez}, SZ: {SZ},
      ex₀: {ex₀}, ey₀: {ey₀}, ez₀: {ez₀}"
    | .AssociatorInv ex SX ey SY ez SZ ex₀ ey₀ ez₀ =>
      m!"Associator inv with ex: {ex}, SX: {SX}, ey: {ey}, SY: {SY}, ez: {ez}, SZ: {SZ},
      ex₀: {ex₀}, ey₀: {ey₀}, ez₀: {ez₀}"
    | .BraidingHom ex SX ey SY =>
      m!"Braiding hom with ex: {ex}, SX: {SX}, ey: {ey}, SY: {SY}"

/-- Unfold kernel operations in an expression. -/
def unfoldKernelOp (e : Expr) : MetaM Expr := do
  let names := (.empty |> NameSet.insert <| ``Kernel.prod) |> NameSet.insert <| ``Kernel.compProd
  transform e (post := fun e => do
    let e' ← deltaExpand e names.contains
    let e' ← Core.betaReduce e'
    return .done e')
