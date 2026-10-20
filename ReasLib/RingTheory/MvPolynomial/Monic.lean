/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Polynomial.Monic

@[expose] public section

open scoped BigOperators

universe u

/-- A monic polynomial in a distinguished variable is the sum of its leading power and
its lower coefficients expanded over a common finite set of multivariate monomials. -/
theorem Polynomial.Monic.as_sum_monomials {R : Type u} [CommSemiring R] {m : ℕ}
    (Q : Polynomial (MvPolynomial (Fin m) R)) (e : ℕ) (d : Fin m → ℕ)
    (ℒ : Finset (Fin m →₀ ℕ)) (hQ : Q.Monic) (hdegree : Q.natDegree = e)
    (hℒ : ∀ L, L ∈ ℒ ↔ ∀ i, L i ≤ d i)
    (hsupport : ∀ l < e, (Q.coeff l).support ⊆ ℒ) :
    Q = Polynomial.X ^ e +
      ∑ l ∈ Finset.range e,
        Polynomial.C
            (∑ L ∈ ℒ, MvPolynomial.monomial L (MvPolynomial.coeff L (Q.coeff l))) *
          Polynomial.X ^ l := sorry
