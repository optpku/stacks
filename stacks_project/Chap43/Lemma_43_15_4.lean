module

public import ReasLib.RingTheory.Polynomial.FiniteDifference
import StacksCheckRecall

open scoped BigOperators Polynomial

universe u

/- Lemma 43.15.4: if `P` has degree `r`, then its leading coefficient multiplied by
`r!` is the alternating binomial sum of the values `P.eval (t - i)` for `0 ≤ i ≤ r`. -/
@[stacks 0AZY] #check (Polynomial.factorial_mul_leadingCoeff_eq_sum_eval_sub :
  ∀ {R : Type u} [CommRing R] (P : R[X]) (r : ℕ), P.degree = r → ∀ t : R,
    (r.factorial : R) * P.leadingCoeff =
      ∑ i ∈ Finset.range (r + 1),
        (-1 : R) ^ i * (r.choose i : R) * P.eval (t - (i : R)))
