/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Lean

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

/-- Recursively traverse an expression and collect universe levels found.
Returns a list of all universe levels encountered. -/
partial def collectKernelUniverses (e : Expr) : MetaM (List Level) :=
  let aux (e: Expr) : MetaM (List Level) := do
    let eType ← inferType e
    let mut levels : List Level := []
    match eType.getAppFn with
    | Expr.const _ univs =>
      -- univs contains the universe levels for this kernel
      levels := univs
    | _ => pure ()
    match e with
    | Expr.app f a =>
      let levelsF ← collectKernelUniverses f
      let levelsA ← collectKernelUniverses a
      return levels ++ levelsF ++ levelsA
    | _ => return levels
  return (← aux e).eraseDups

def compute_max_universe (levels : List Level) : MetaM Level :=
  match levels with
    | [] => throwError "No universe levels found in the expression"
    | head :: tail => pure (tail.foldl Level.max head)
