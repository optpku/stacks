/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.KrullDimension.Polynomial.Intersection

@[expose] public section

open TopologicalSpace

universe u

/- Lemma 33.34.2: let `k` be a field and `n ≥ 0`. If the closed subsets
`V(I)` and `V(J)` of affine `n`-space are equidimensional of dimensions `r` and `s`, then every
irreducible component of their intersection `V(I ⊔ J)` has dimension at least `r + s - n`. -/
@[stacks 0B2Q] #check
  (MvPolynomial.topologicalKrullDim_irreducibleComponent_quotient_sup_ge_add_sub :
    ∀ {k : Type u} [Field k] (n r s : ℕ) (I J : Ideal (MvPolynomial (Fin n) k))
      [EquidimensionalSpace (PrimeSpectrum (MvPolynomial (Fin n) k ⧸ I))]
      [EquidimensionalSpace (PrimeSpectrum (MvPolynomial (Fin n) k ⧸ J))],
      topologicalKrullDim (PrimeSpectrum (MvPolynomial (Fin n) k ⧸ I)) =
          ((r : ℕ) : WithBot ℕ∞) →
        topologicalKrullDim (PrimeSpectrum (MvPolynomial (Fin n) k ⧸ J)) =
            ((s : ℕ) : WithBot ℕ∞) →
          ∀ Z : irreducibleComponents (PrimeSpectrum (MvPolynomial (Fin n) k ⧸ (I ⊔ J))),
            ((r + s - n : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim Z)
