module

import Mathlib.Tactic
import Lean

@[expose] public section

namespace PrimeToTraceArithmetic

/-- Once integrality and the first two exact point-count equations are proved,
the unconditional bound has an allowed upper endpoint and excluded lower endpoint. -/
theorem bounds_of_first_two_counts (q s₁ s₂ : ℕ) (a : ℤ)
    (hq : 1 ≤ q) (h₁ : (q : ℤ) - a = s₁)
    (h₂ : (q : ℤ) ^ 2 - a ^ 2 = (s₁ : ℤ) + 2 * s₂) :
    -(q : ℤ) < a ∧ a ≤ q := by
  have hqpos : (0 : ℤ) < q := by omega
  have hs₁ : (0 : ℤ) ≤ s₁ := by omega
  have hs₂ : (0 : ℤ) ≤ s₂ := by omega
  constructor
  · by_contra ha
    have hsum : a + q ≤ 0 := by omega
    have hdiff : a - q ≤ 0 := by omega
    have hproduct := mul_nonneg_of_nonpos_of_nonpos hsum hdiff
    nlinarith
  · omega

/-- Strictness is precisely positivity of the degree-one count after the exact equations. -/
theorem strict_iff_degree_one_nonempty (q s₁ s₂ : ℕ) (a : ℤ)
    (hq : 1 ≤ q) (h₁ : (q : ℤ) - a = s₁)
    (h₂ : (q : ℤ) ^ 2 - a ^ 2 = (s₁ : ℤ) + 2 * s₂) :
    a.natAbs < q ↔ 0 < s₁ := by
  have bounds := bounds_of_first_two_counts q s₁ s₂ a hq h₁ h₂
  omega

/-- The upper endpoint corresponds exactly to the zero degree-one count. -/
theorem upper_endpoint_iff (q s₁ : ℕ) (a : ℤ)
    (h₁ : (q : ℤ) - a = s₁) : a = q ↔ s₁ = 0 := by
  omega

end PrimeToTraceArithmetic
