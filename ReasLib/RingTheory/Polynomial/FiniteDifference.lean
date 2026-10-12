/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Group.ForwardDiff

@[expose] public section

open scoped BigOperators

universe u

namespace Polynomial

/-- The factorial-scaled leading coefficient of a polynomial of degree `r` is the
alternating binomial sum of its values at the backward shifts `t - i` for `0 ≤ i ≤ r`. -/
public theorem factorial_mul_leadingCoeff_eq_sum_eval_sub {R : Type u} [CommRing R]
    (P : R[X]) (r : ℕ) (h_degree : P.degree = r) (t : R) :
    (r.factorial : R) * P.leadingCoeff =
      ∑ i ∈ Finset.range (r + 1),
        (-1 : R) ^ i * (r.choose i : R) * P.eval (t - (i : R)) := sorry

end Polynomial
