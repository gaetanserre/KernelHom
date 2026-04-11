/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Lean

/-!
# Universe level utilities

This file provides utilities for working with universe levels in metaprograms.
It includes conversion functions between levels and syntax, and universe level collection.

## Main declarations

- `levelToSyntax`: converts a `Level` to quotable syntax.
- `collectExprUniverses`: recursively collects universe levels from expressions.
- `get_universe_from_eq`: extracts universe information from categorical equalities.
-/

open Lean Meta

/-- Convert a Level to Syntax for use in tactic quotations. -/
partial def levelToSyntax (lvl : Level) : MacroM (TSyntax `level) := do
  match lvl with
  | Level.zero => `(level| 0)
  | Level.succ l =>
    let lStx : TSyntax `level ← levelToSyntax l
    `(level| $lStx + 1)
  | Level.param n => `(level| $(mkIdent n):ident)
  | Level.mvar _ => Macro.throwError "Cannot convert mvar level to syntax"
  | Level.max l1 l2 =>
    let l1Stx : TSyntax `level ← levelToSyntax l1
    let l2Stx : TSyntax `level ← levelToSyntax l2
    `(level| max $l1Stx $l2Stx)
  | Level.imax l1 l2 =>
    let l1Stx : TSyntax `level ← levelToSyntax l1
    let l2Stx : TSyntax `level ← levelToSyntax l2
    `(level| imax $l1Stx $l2Stx)

/-- Recursively traverses an expression and collects all universe levels. -/
private def collectExprUniverses.aux (e : Expr) : List Level :=
  match e with
  | Expr.const _ univs => univs
  | Expr.sort u => [u]
  | Expr.app f a => aux f ++ aux a
  | Expr.lam _ t b _ => aux t ++ aux b
  | Expr.forallE _ t b _ => aux t ++ aux b
  | Expr.letE _ t v b _ => aux t ++ aux v ++ aux b
  | Expr.mdata _ b => aux b
  | Expr.proj _ _ b => aux b
  | Expr.bvar _ | Expr.fvar _ | Expr.mvar _ | Expr.lit _ => []

/-- Recursively traverse an expression and collect universe levels found.
Returns a list of all unique universe levels encountered. -/
partial def collectExprUniverses (e : Expr) : MetaM (List Level) := do
  let e ← instantiateMVars e
  let e ← zetaReduce e
  return (collectExprUniverses.aux e).eraseDups

/-- Compute the maximum universe level from a list of levels. -/
def compute_max_universe (levels : List Level) : MetaM Level :=
  match levels with
    | [] => throwError "Expected at least one universe level, got an empty list"
    | head :: tail => pure (tail.foldl Level.max head)

/-- Get the category universe level from the left side of an equality expression. -/
def get_universe_from_eq (eq : Expr) : MetaM Level := do
  let eq ← instantiateMVars eq
  let eq ← zetaReduce eq
  let eq ← whnf eq
  let eq := eq.consumeMData
  match eq with
  | Expr.app (Expr.app (Expr.app (Expr.const ``Eq _) _) lhsExpr) _ =>
    let l ← getLevel (← inferType lhsExpr)
    match l with
    | Level.succ l' => return l'
    | _ => throwError "Expected a universe level ≥ 1, got: {l}"
  | _ =>
    throwError "Expected an equality, got: {eq}"
