/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
import KernelHomTests.Basu
import KernelHomTests.Examples

/-!
# Scope of the tactics on the structural lemmas of Mathlib

The candidates are the equalities of kernels of `Mathlib.Probability.Kernel.Composition.Comp`,
`CompMap`, `ParallelComp`, `Prod`, `KernelLemmas` and of `Mathlib.Probability.Kernel.Deterministic`
whose two sides are built from kernel variables with `∘ₖ`, `∥ₖ`, `×ₖ`, `Kernel.id`, `copy`,
`discard`, `swap`, the image by `Kernel.map` of `Prod.swap`, `prodComm` or `prodAssoc`, the
marginals `fst` and `snd`, and the deterministic kernels of the projections `Prod.fst` and
`Prod.snd`. The definitional lemma `parallelComp_comp_copy` (the definition of `×ₖ`) and the
rewriting lemma `swap_comp_eq_map` (`swap β γ ∘ₖ κ = κ.map Prod.swap`, used to state the other
lemmas in the vocabulary of the tactics) are excluded. There are 26 of them.

* 7 are not used by the construction of `SFinKer`, Eq-Lift or Kernel-Hom, and are proved in
  `KernelHomTests/Examples.lean`, without depending on the lemma they re-prove (checked below by
  `#assert_not_depends_on`) and with the standard axioms only (`#print axioms`).
* 13 are used by the construction of `SFinKer`, Eq-Lift or Kernel-Hom (checked below by
  `#assert_used_by_machinery`). The tactics prove them, but the proofs depend on the lemma itself.
* 6 are not proved by the tactics (`fail_if_success` below): the marginals `fst` and `snd`, and
  `deterministic Prod.fst`, are not translated, and positivity is not used by `kernel_disch`.

This file is not a module: a module does not import the proofs of the theorems of other modules,
which the dependency checks below need.
-/

open Lean Elab Command

set_option linter.hashCommand false

/-- The constants used, transitively, by the type and the value of the constants `roots`. -/
partial def transitiveDeps (env : Environment) (roots : List Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := roots
  while !todo.isEmpty do
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      if seen.contains n then continue
      seen := seen.insert n
      if let some ci := env.find? n then
        for m in ci.getUsedConstantsAsSet do
          if !seen.contains m then todo := m :: todo
  return seen

/-- `#assert_not_depends_on d l` fails if the declaration `d` depends, transitively, on `l`. -/
elab "#assert_not_depends_on " d:ident l:ident : command => do
  let env ← getEnv
  let d ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let l ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo l
  if (transitiveDeps env [d]).contains l then throwError "{d} depends on {l}"

/-- `#assert_depends_on d l` fails if the declaration `d` does not depend, transitively, on `l`.
It is the positive control of `#assert_not_depends_on`: it checks that the traversal sees the
proofs of the theorems, without which `#assert_not_depends_on` would hold vacuously. -/
elab "#assert_depends_on " d:ident l:ident : command => do
  let env ← getEnv
  let d ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let l ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo l
  unless (transitiveDeps env [d]).contains l do throwError "{d} does not depend on {l}"

/-- `#assert_used_by_machinery l₁ ... lₙ` fails if one of the `lᵢ` is not used, transitively, by
a declaration of `Mathlib.Probability.Kernel.Category`, Eq-Lift or Kernel-Hom. The transitive
closure is computed once for all the `lᵢ`. -/
elab "#assert_used_by_machinery " ls:ident+ : command => do
  let env ← getEnv
  let roots := env.constants.toList.filterMap fun (n, _) => do
    let idx ← env.getModuleIdxFor? n
    let m := env.header.moduleNames[idx.toNat]!
    if (`Mathlib.Probability.Kernel.Category).isPrefixOf m || (`KernelHom).isPrefixOf m ||
      (`EqLift).isPrefixOf m then some n else none
  let deps := transitiveDeps env roots
  for l in ls do
    let l ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo l
    unless deps.contains l do throwError "{l} is not used by the machinery"

open MeasureTheory ProbabilityTheory CategoryTheory MonoidalCategory

namespace ProbabilityTheory.Kernel

/-! ### The lemmas of `KernelHomTests/Examples.lean` and `basu` do not depend on Mathlib's proofs

Positive controls first: the traversal sees the proofs of Mathlib, of Kernel-Hom and of the test
files. -/

#assert_depends_on swap_prod map_prod_swap
#assert_depends_on swap_prod₀ toHom_congr
#assert_depends_on swap_prod₀ braiding_hom
#assert_depends_on prodComm_prod₀ swap_comp_eq_map
#assert_depends_on basu basu_aux


#assert_not_depends_on map_prod_swap₀ map_prod_swap
#assert_not_depends_on swap_prod₀ swap_prod
#assert_not_depends_on prodAssoc_prod₀ prodAssoc_prod
#assert_not_depends_on prodAssoc_symm_prod₀ prodAssoc_symm_prod
#assert_not_depends_on prodComm_prod₀ prodComm_prod
#assert_not_depends_on parallelComp_comp_prod₀ parallelComp_comp_prod
#assert_not_depends_on parallelComp_comm₀ parallelComp_comm
#assert_not_depends_on basu swap_prod
#assert_not_depends_on basu parallelComp_comp_prod

/-! ### They only use the standard axioms -/

/--
info: 'ProbabilityTheory.Kernel.map_prod_swap₀' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms map_prod_swap₀

/--
info: 'ProbabilityTheory.Kernel.swap_prod₀' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms swap_prod₀

/--
info: 'ProbabilityTheory.Kernel.prodAssoc_prod₀' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prodAssoc_prod₀

/--
info: 'ProbabilityTheory.Kernel.prodAssoc_symm_prod₀' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prodAssoc_symm_prod₀

/--
info: 'ProbabilityTheory.Kernel.prodComm_prod₀' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prodComm_prod₀

/--
info: 'ProbabilityTheory.Kernel.parallelComp_comp_prod₀' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms parallelComp_comp_prod₀

/--
info: 'ProbabilityTheory.Kernel.parallelComp_comm₀' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms parallelComp_comm₀

/--
info: 'ProbabilityTheory.Kernel.basu' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms basu

/-! ### Lemmas used by the construction: proved by the tactics, but not independently -/

#assert_used_by_machinery
  id_comp
  comp_id
  comp_assoc
  comp_discard
  swap_copy
  swap_swap
  id_parallelComp_id
  swap_parallelComp
  parallelComp_id_left_comp_parallelComp
  parallelComp_id_right_comp_parallelComp
  parallelComp_comp_parallelComp
  id_parallelComp_comp_parallelComp_id
  parallelComp_self_comp_copy

variable {X Y Z T X' Y' Z' : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  [MeasurableSpace T] [MeasurableSpace X'] [MeasurableSpace Y'] [MeasurableSpace Z']

example (κ : Kernel X Y) [IsSFiniteKernel κ] : Kernel.id ∘ₖ κ = κ := by kernel_disch
example (κ : Kernel X Y) [IsSFiniteKernel κ] : κ ∘ₖ Kernel.id = κ := by kernel_disch
example (κ : Kernel X Y) (η : Kernel Y Z) (ξ : Kernel Z T) [IsSFiniteKernel κ]
    [IsSFiniteKernel η] [IsSFiniteKernel ξ] : ξ ∘ₖ η ∘ₖ κ = ξ ∘ₖ (η ∘ₖ κ) := by kernel_disch
example (κ : Kernel X Y) [IsMarkovKernel κ] : discard Y ∘ₖ κ = discard X := by kernel_disch
example : swap X X ∘ₖ copy X = copy X := by kernel_disch
example : swap X Y ∘ₖ swap Y X = Kernel.id := by kernel_disch
example : (Kernel.id : Kernel X X) ∥ₖ (Kernel.id : Kernel Y Y) = Kernel.id := by kernel_disch
example {κ : Kernel X Y} {η : Kernel Z T} [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    swap Y T ∘ₖ (κ ∥ₖ η) = η ∥ₖ κ ∘ₖ swap X Z := by kernel_disch
example {κ : Kernel X Y} [IsSFiniteKernel κ] {η : Kernel X' Z} [IsSFiniteKernel η]
    {ξ : Kernel Z T} [IsSFiniteKernel ξ] :
    (Kernel.id ∥ₖ ξ) ∘ₖ (κ ∥ₖ η) = κ ∥ₖ (ξ ∘ₖ η) := by kernel_disch
example {κ : Kernel X Y} [IsSFiniteKernel κ] {η : Kernel X' Z} [IsSFiniteKernel η]
    {ξ : Kernel Z T} [IsSFiniteKernel ξ] :
    (ξ ∥ₖ Kernel.id) ∘ₖ (η ∥ₖ κ) = (ξ ∘ₖ η) ∥ₖ κ := by kernel_disch
example {κ : Kernel X Y} [IsSFiniteKernel κ] {η : Kernel Y Z} [IsSFiniteKernel η]
    {κ' : Kernel X' Y'} [IsSFiniteKernel κ'] {η' : Kernel Y' Z'} [IsSFiniteKernel η'] :
    (η ∥ₖ η') ∘ₖ (κ ∥ₖ κ') = (η ∘ₖ κ) ∥ₖ (η' ∘ₖ κ') := by kernel_disch
example {κ : Kernel X Y} [IsSFiniteKernel κ] {η : Kernel Z T} [IsSFiniteKernel η] :
    Kernel.id ∥ₖ κ ∘ₖ (η ∥ₖ Kernel.id) = η ∥ₖ κ := by kernel_disch
example (κ : Kernel X Y) [IsMarkovKernel κ] [IsDeterministic κ] :
    (κ ∥ₖ κ) ∘ₖ copy X = copy Y ∘ₖ κ := by kernel_disch

/-! ### Lemmas that the tactics do not prove -/

example (κ : Kernel X Y) (η : Kernel Y (Z × T)) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    (η ∘ₖ κ).fst = η.fst ∘ₖ κ := by
  fail_if_success kernel_disch
  exact fst_comp κ η

example (κ : Kernel X Y) (η : Kernel Y (Z × T)) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    (η ∘ₖ κ).snd = η.snd ∘ₖ κ := by
  fail_if_success kernel_disch
  exact snd_comp κ η

example (κ : Kernel X Y) [IsSFiniteKernel κ] (η : Kernel X Z) [IsMarkovKernel η] :
    fst (κ ×ₖ η) = κ := by
  fail_if_success kernel_disch
  exact fst_prod κ η

example (κ : Kernel X Y) [IsMarkovKernel κ] (η : Kernel X Z) [IsSFiniteKernel η] :
    snd (κ ×ₖ η) = η := by
  fail_if_success kernel_disch
  exact snd_prod κ η

example : @Kernel.id (X × Y) inferInstance =
    (deterministic Prod.fst measurable_fst) ×ₖ (deterministic Prod.snd measurable_snd) := by
  fail_if_success kernel_disch
  exact id_prod_eq

example {κ : Kernel X Y} {η : Kernel Y Z} [IsMarkovKernel κ] [IsMarkovKernel η]
    [IsDeterministic (η ∘ₖ κ)] :
    ((η ∘ₖ κ) ∥ₖ κ) ∘ₖ copy X = (η ∥ₖ Kernel.id) ∘ₖ copy Y ∘ₖ κ := by
  fail_if_success kernel_disch
  exact comp_parallelComp_comp_copy

end ProbabilityTheory.Kernel
