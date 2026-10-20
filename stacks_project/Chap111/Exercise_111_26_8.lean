module

public import ReasLib.RingTheory.MvPolynomial.WeightedHilbert
import StacksCheckRecall

/-!
# Hilbert function of k[x, y] with weights 2 and 3

This file records the Hilbert function of `k[x, y]` graded by `deg(x) = 2` and `deg(y) = 3`,
with Euler-Poincaré function `φ(M) = dim_k(M)`, and the fact that this graded module has no
Hilbert polynomial.
-/

@[expose] public section

universe u

open MvPolynomial CategoryTheory.ModuleCat GradedModule

/- Exercise 111.26.8 (1): for a field `k`, writing `A = k` and `B = k[x, y]` graded by
`deg(x) = 2` and `deg(y) = 3`, and taking `φ(M) = dim_k(M)`, the Hilbert function of `B` as a
graded `k`-module is `0` for `n < 0` and `n / 6 + if n % 6 = 1 then 0 else 1` for `n ≥ 0`. -/
@[stacks 02E6] #check (MvPolynomial.Weights23.hilbertFunction_eq :
  ∀ (k : Type u) [Field k] (n : ℤ),
    hilbertFunction (K0.Finite.genericRank.{u, u} k)
      (MvPolynomial.Weights23.integerGrading k) n =
        if n < 0 then 0 else n / 6 + if n % 6 = 1 then 0 else 1)

/- Exercise 111.26.8 (2): for a field `k`, writing `A = k` and `B = k[x, y]` graded by
`deg(x) = 2` and `deg(y) = 3`, and taking `φ(M) = dim_k(M)`, the graded `k`-module `B` has no
Hilbert polynomial. -/
@[stacks 02E6] #check (MvPolynomial.Weights23.not_hasHilbertPolynomial :
  ∀ (k : Type u) [Field k],
    ¬ HasHilbertPolynomial (K0.Finite.genericRank.{u, u} k)
      (MvPolynomial.Weights23.integerGrading k))

#check (MvPolynomial.Weights23.hilbertFunction_eq_finrank :
  ∀ (k : Type u) [Field k] (n : ℤ),
    hilbertFunction (K0.Finite.genericRank.{u, u} k)
      (MvPolynomial.Weights23.integerGrading k) n =
        Module.finrank k (MvPolynomial.Weights23.integerGrading k n))

#check (MvPolynomial.Weights23.hilbertFunction_eq_card :
  ∀ (k : Type u) [Field k] {n : ℤ}, 0 ≤ n →
    hilbertFunction (K0.Finite.genericRank.{u, u} k)
      (MvPolynomial.Weights23.integerGrading k) n =
        Nat.card {p : ℕ × ℕ | 2 * p.1 + 3 * p.2 = n.toNat})
