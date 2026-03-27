# Kernel-Hom

Lean 4 project focused on tactics that translate kernel equalities into categorical equalities, and back. This work is still in early stages, but the core tactics are already implemented and can be used to simplify kernel equalities by leveraging categorical reasoning.

<p align="center">
  <img src="diagram/diagram.svg" width="500">
</p>

## Status

This repository is mainly about the tactics `kernel_hom` and `hom_kernel`.

They are built on top of `SFinKer`, the category of measurable spaces with s-finite kernels as morphisms. This categorical layer is the key reason the tactic workflow works.

Very briefly, the tactics:

- translate an equality of kernels into an equality in categorical/monoidal form,
- let you run category-theory tactics such as `coherence` or `monoidal`,
- translate the result back to a kernel equality.

Universe handling is part of this translation: expressions are lifted to a common universe level, so rewrites stay well-typed across universe levels.

In addition, `SFinKer` also gives a direct route to `Stoch`, the Markov category of measurable spaces and Markov kernels, defined as the wide subcategory of `SFinKer` with Markov kernels as morphisms. The definitions/results for `SFinKer` and `Stoch` are now in mathlib (PR [#36779](https://github.com/leanprover-community/mathlib4/pull/36779)) but are also included here for ease of development and maintenance, alongside the tactics.

## Repository contents

### 1) Tactics

- [KernelHom.lean](KernelHom/Tactic/Hom/KernelHom.lean):
  implementation of `kernel_hom` (transforms kernel equalities into monoidal category equalities).
- [HomKernel.lean](KernelHom/Tactic/Hom/HomKernel.lean):
  implementation of `hom_kernel` (inverse transformation back to kernel equalities).
- [KernelCoherence.lean](KernelHom/Tactic/KernelCoherence.lean):
  helpers built on top of the translations (`kernel_coherence`, `kernel_monoidal`).
- [Tactics.lean](KernelHom/Tactic/Tactics.lean):
  import hub for the tactic layer.

### 2) Categorical/probabilistic backbone

- [SFinKer.lean](KernelHom/Mathlib/CategoryTheory/Kernel/SFinKer.lean):
  definition of `SFinKer` and instances `LargeCategory`, `MonoidalCategory`, `SymmetricCategory`, `CopyDiscardCategory`.
- [Stoch.lean](KernelHom/Mathlib/CategoryTheory/Kernel/Stoch.lean):
  definition of `Stoch` as a wide subcategory of `SFinKer` (Markov morphisms) and instance `MarkovCategory`.
- [Kernel.lean](KernelHom/Mathlib/Kernel.lean), [LIntegral.lean](KernelHom/Mathlib/LIntegral.lean), [MeasurableEquiv.lean](KernelHom/Mathlib/MeasurableEquiv.lean):
  auxiliary lemmas used by the constructions above.

### 3) Examples and ongoing work

- [Tests.lean](KernelHom/Tests.lean): examples using `kernel_hom` and `hom_kernel`.
- [Posterior.lean](Posterior.lean): exploratory developments on posterior kernels.

## Usage

```bash
lake build
```

In a Lean file:

```lean
import KernelHom
```

Or, for tactics only:

```lean
import KernelHom.Tactic.Tactics
```

## Reference

- Tobias Fritz. *A synthetic approach to Markov kernels, conditional independence and theorems on sufficient statistics*. Adv. Math. **370** (2020), 107239. [arXiv:1908.07021](https://arxiv.org/abs/1908.07021).

## License

GNU GPL 3.0. See [LICENSE](LICENSE).