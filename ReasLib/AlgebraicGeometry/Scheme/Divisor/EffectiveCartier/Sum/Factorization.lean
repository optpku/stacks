/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Sum.Effective

/-!
# Factoring inclusions of effective Cartier divisors

An inclusion of effective Cartier divisors can be factored as a divisor sum.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (D D' : X.IdealSheafData)

/-- An inclusion of effective Cartier divisors factors through a third effective Cartier divisor
under the divisor-sum operation. -/
theorem exists_eq_effectiveCartierDivisorSum_of_le
    [IsEffectiveCartierDivisor D.subschemeι]
    [IsEffectiveCartierDivisor D'.subschemeι] (hle : D' ≤ D) :
    ∃ D'' : X.IdealSheafData,
      IsEffectiveCartierDivisor D''.subschemeι ∧
        D' = effectiveCartierDivisorSum D D'' := sorry

/-- The corresponding factorization of ideal sheaves as a product. -/
theorem exists_ideal_eq_mul_of_le
    [IsEffectiveCartierDivisor D.subschemeι]
    [IsEffectiveCartierDivisor D'.subschemeι] (hle : D' ≤ D) :
    ∃ D'' : X.IdealSheafData,
      IsEffectiveCartierDivisor D''.subschemeι ∧
        D'.ideal = D.ideal * D''.ideal := by
  rcases exists_eq_effectiveCartierDivisorSum_of_le D D' hle with
    ⟨D'', hD'', hsum⟩
  refine ⟨D'', hD'', ?_⟩
  simpa [hsum] using ideal_effectiveCartierDivisorSum D D''

end AlgebraicGeometry.Scheme.IdealSheafData
