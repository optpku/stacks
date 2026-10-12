/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Sum

/-!
# Effectivity of sums of effective Cartier divisors

This file owns the closure of effective Cartier divisors under sums.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry
namespace Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- The product of two effective Cartier divisor ideal sheaves is again effective Cartier. -/
theorem isEffectiveCartierDivisor_mul
    (D₁ D₂ : X.IdealSheafData)
    [IsEffectiveCartierDivisor D₁.subschemeι]
    [IsEffectiveCartierDivisor D₂.subschemeι] :
    IsEffectiveCartierDivisor (D₁ * D₂).subschemeι := sorry

/-- The sum of two effective Cartier divisor ideal sheaves is again effective Cartier. -/
theorem isEffectiveCartierDivisor_sum
    (D₁ D₂ : X.IdealSheafData)
    [IsEffectiveCartierDivisor D₁.subschemeι]
    [IsEffectiveCartierDivisor D₂.subschemeι] :
    IsEffectiveCartierDivisor (effectiveCartierDivisorSum D₁ D₂).subschemeι := by
  simpa [effectiveCartierDivisorSum] using isEffectiveCartierDivisor_mul D₁ D₂

/-- The sum of two effective Cartier divisor ideal sheaves carries the canonical effective
Cartier divisor instance. -/
instance instIsEffectiveCartierDivisorSum
    (D₁ D₂ : X.IdealSheafData)
    [IsEffectiveCartierDivisor D₁.subschemeι]
    [IsEffectiveCartierDivisor D₂.subschemeι] :
    IsEffectiveCartierDivisor (effectiveCartierDivisorSum D₁ D₂).subschemeι :=
  isEffectiveCartierDivisor_sum D₁ D₂

end Scheme.IdealSheafData
end AlgebraicGeometry
