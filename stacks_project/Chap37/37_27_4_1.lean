/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.MvPolynomial.Monic

@[expose] public section

open scoped BigOperators

universe u

/- 37.27.4.1: A monic polynomial in the distinguished variable has an expansion whose
lower coefficients use the common set of coordinatewise bounded multivariate monomials. -/
@[stacks 0558] #check
  (Polynomial.Monic.as_sum_monomials :
    ∀ {R : Type u} [CommSemiring R] {m : ℕ}
      (Q : Polynomial (MvPolynomial (Fin m) R)) (e : ℕ) (d : Fin m → ℕ)
      (ℒ : Finset (Fin m →₀ ℕ)),
      Q.Monic → Q.natDegree = e →
      (∀ L, L ∈ ℒ ↔ ∀ i, L i ≤ d i) →
      (∀ l < e, (Q.coeff l).support ⊆ ℒ) →
      Q = Polynomial.X ^ e +
        ∑ l ∈ Finset.range e,
          Polynomial.C
              (∑ L ∈ ℒ, MvPolynomial.monomial L (MvPolynomial.coeff L (Q.coeff l))) *
            Polynomial.X ^ l)
