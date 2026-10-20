module

public import Mathlib.Algebra.Polynomial.Degree.Defs

@[expose]
public section

universe u

namespace Polynomial

variable {R : Type u} [CommRing R]

/-- For a polynomial with natural degree at most `d`, scaling any dividend by
a power of its coefficient at `d` gives a remainder of degree less than `d`. -/
theorem exists_C_pow_mul_eq_mul_add_of_natDegree_le (f : R[X]) (d : ℕ)
    (hf : f.natDegree ≤ d) (g : R[X]) :
    ∃ (N : ℕ) (q r : R[X]),
      C (f.coeff d) ^ N * g = q * f + r ∧ r.degree < d := sorry

/-- For a polynomial with natural degree at most `d`, scaling any dividend by
a power of its coefficient at `d` gives a remainder whose coefficients vanish
at all indices at least `d`. -/
theorem exists_C_pow_mul_eq_mul_add_of_natDegree_le_coeff (f : R[X]) (d : ℕ)
    (hf : f.natDegree ≤ d) (g : R[X]) :
    ∃ (N : ℕ) (q r : R[X]),
      C (f.coeff d) ^ N * g = q * f + r ∧ ∀ n, d ≤ n → r.coeff n = 0 := sorry

/-- Scaling a dividend by a power of the divisor's leading coefficient gives
a remainder of degree strictly less than the divisor's natural degree. -/
theorem exists_C_leadingCoeff_pow_mul_eq_mul_add (f g : R[X]) :
    ∃ (N : ℕ) (q r : R[X]),
      C (f.leadingCoeff) ^ N * g = q * f + r ∧ r.degree < f.natDegree := sorry

end Polynomial
