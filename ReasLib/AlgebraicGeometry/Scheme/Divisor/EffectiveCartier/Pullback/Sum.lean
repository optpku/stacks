/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Sum.Effective

/-!
# Pullbacks of sums of effective Cartier divisors

This file records the compatibility of inverse-image ideal-sheaf data with sums of effective
Cartier divisors.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme.IdealSheafData

variable {S S' : Scheme.{u}}

/-- Inverse image commutes with the sum of two effective Cartier divisor ideal sheaves. -/
theorem comap_effectiveCartierDivisorSum
    (f : S' ⟶ S) (D₁ D₂ : S.IdealSheafData) :
    (effectiveCartierDivisorSum D₁ D₂).comap f =
      effectiveCartierDivisorSum (D₁.comap f) (D₂.comap f) := sorry

/-- The inverse image of a sum is canonically an effective Cartier divisor whenever the
inverse images of both summands are effective Cartier divisors. -/
instance instIsEffectiveCartierDivisorComapSum
    (f : S' ⟶ S) (D₁ D₂ : S.IdealSheafData)
    [IsEffectiveCartierDivisor (D₁.comap f).subschemeι]
    [IsEffectiveCartierDivisor (D₂.comap f).subschemeι] :
    IsEffectiveCartierDivisor
      ((effectiveCartierDivisorSum D₁ D₂).comap f).subschemeι := by
  rw [comap_effectiveCartierDivisorSum]
  infer_instance

/-- If two effective Cartier divisors have defined pullbacks, then their sum also has a
defined pullback. -/
theorem pullbackDefined_effectiveCartierDivisorSum
    (f : S' ⟶ S) (D₁ D₂ : S.IdealSheafData)
    [IsEffectiveCartierDivisor D₁.subschemeι]
    [IsEffectiveCartierDivisor D₂.subschemeι]
    (hD₁ : pullbackDefined D₁ f) (hD₂ : pullbackDefined D₂ f) :
    pullbackDefined (effectiveCartierDivisorSum D₁ D₂) f :=
  @instIsEffectiveCartierDivisorComapSum S S' f D₁ D₂ hD₁ hD₂

/-- If two effective Cartier divisors have defined pullbacks, then the pullback of their sum
is the sum of their pullbacks. -/
theorem comap_effectiveCartierDivisorSum_of_pullbackDefined
    (f : S' ⟶ S) (D₁ D₂ : S.IdealSheafData)
    [IsEffectiveCartierDivisor D₁.subschemeι]
    [IsEffectiveCartierDivisor D₂.subschemeι]
    (hD₁ : pullbackDefined D₁ f) (hD₂ : pullbackDefined D₂ f) :
    (effectiveCartierDivisorSum D₁ D₂).comap f =
      effectiveCartierDivisorSum (D₁.comap f) (D₂.comap f) :=
  comap_effectiveCartierDivisorSum f D₁ D₂

end Scheme.IdealSheafData
end AlgebraicGeometry
