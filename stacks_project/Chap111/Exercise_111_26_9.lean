module

public import ReasLib.RingTheory.MvPolynomial.Weights23Quotient
import StacksCheckRecall

/-!
# Hilbert function of k[x, y]/(x^2, xy) with weights 2 and 3

This file checks the Hilbert function of `k[x, y] ⧸ (x ^ 2, x * y)` graded by `deg(x) = 2` and
`deg(y) = 3`, with Euler-Poincaré function `φ(M) = dim_k(M)`, and the fact that this graded module
has no Hilbert polynomial.
-/

@[expose] public section

universe u

/- Exercise 111.26.9 (1): the Hilbert function of the weighted quotient. -/
@[stacks 02E7]
#check (MvPolynomial.Weights23Quotient.hilbertFunction_eq :
    ∀ (k : Type u) [Field k] (n : ℤ),
  GradedModule.hilbertFunction
    (CategoryTheory.ModuleCat.K0.Finite.genericRank.{u, u} k)
    (MvPolynomial.Weights23Quotient.integerGrading k) n =
      if n = 2 ∨ (0 ≤ n ∧ 3 ∣ n) then 1 else 0)

/- Exercise 111.26.9 (2): the weighted quotient has no Hilbert polynomial. -/
@[stacks 02E7]
#check (MvPolynomial.Weights23Quotient.not_hasHilbertPolynomial :
  ∀ (k : Type u) [Field k],
    ¬ GradedModule.HasHilbertPolynomial
        (CategoryTheory.ModuleCat.K0.Finite.genericRank.{u, u} k)
        (MvPolynomial.Weights23Quotient.integerGrading k))
