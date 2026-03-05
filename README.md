# LeanStoch

A formalization of the Markov category **Stoch** in Lean 4.

<p align="center">
  <img src="diagram/diagram.svg" width="500">
</p>

## Overview

This library provides a rigorous formalization of the category [**Stoch**](https://ncatlab.org/nlab/show/Stoch) whose:
- **Objects** are measurable spaces.
- **Morphisms** are Markov kernels (s-finite kernels with `kernel x` being a probability measure for each `x`).

We prove that **Stoch** forms a Markov category ([Fritz, 2020](https://arxiv.org/abs/1908.07021)) by establishing:
1. **Stoch** is a symmetric monoidal category with monoidal product given by the Cartesian product.
2. Every object carries a canonical comonoid structure (copying and discarding).
3. The copy and discard morphisms satisfy the coherence axioms of Markov categories.

## Main Results

### Category Structure ([`LeanStoch.Stoch`](LeanStoch/Stoch.lean))

- `instance : LargeCategory Stoch` - Category structure with Markov kernels as morphisms
- `instance : MonoidalCategory Stoch` - Monoidal structure via categorical product  
- `instance : BraidedCategory Stoch` - Braiding from the swap map
- `instance : SymmetricCategory Stoch` - Symmetry of the braiding

### Markov Category Structure

- `instance (X : Stoch) : ComonObj X` - Canonical comonoid on each object
- `instance (X : Stoch) : IsCommComonObj X` - Commutativity of the comonoid
- `instance : MarkovCategory Stoch` - **Stoch** is a Markov category

## Structure

- [`LeanStoch.Stoch`](LeanStoch/Stoch.lean) - Main category definition and Markov category instance
- [`LeanStoch.Tactics`](LeanStoch/Tactics.lean) - Custom tactics for kernel automation (`kernel_markov`, `cat_kernel`)
- [`LeanStoch.Mathlib.Kernel`](LeanStoch/Mathlib/Kernel.lean) - Auxiliary lemmas for probability kernels

## References

- Tobias Fritz. *A synthetic approach to Markov kernels, conditional independence and theorems on sufficient statistics*. Adv. Math. **370** (2020), 107239. [arXiv:1908.07021](https://arxiv.org/abs/1908.07021).

## License

Released under GNU GPL 3.0. See [LICENSE](LICENSE).
