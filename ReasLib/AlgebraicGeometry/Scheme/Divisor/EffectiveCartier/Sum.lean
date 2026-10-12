/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier

/-!
# Sums of effective Cartier divisors

This file owns the sum of two effective Cartier divisors at the ideal-sheaf-data layer.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- The sum of two ideal-sheaf data is defined by their product. -/
def effectiveCartierDivisorSum {X : Scheme.{u}}
    (D₁ D₂ : X.IdealSheafData) : X.IdealSheafData :=
  D₁ * D₂

/-- The sum of two ideal-sheaf data is their product. -/
@[simp] theorem effectiveCartierDivisorSum_eq {X : Scheme.{u}}
    (D₁ D₂ : X.IdealSheafData) :
    effectiveCartierDivisorSum D₁ D₂ = D₁ * D₂ :=
  rfl

/-- The sum of two effective Cartier divisors is their product as ideal-sheaf data. -/
theorem effectiveCartierDivisorSum_spec {X : Scheme.{u}}
    (D₁ D₂ : X.IdealSheafData)
    [IsEffectiveCartierDivisor D₁.subschemeι]
    [IsEffectiveCartierDivisor D₂.subschemeι] :
    effectiveCartierDivisorSum D₁ D₂ = D₁ * D₂ :=
  effectiveCartierDivisorSum_eq D₁ D₂

/-- The ideal sheaf of a divisor sum is the product ideal sheaf. -/
@[simp] theorem ideal_effectiveCartierDivisorSum {X : Scheme.{u}}
    (D₁ D₂ : X.IdealSheafData) :
    (effectiveCartierDivisorSum D₁ D₂).ideal = D₁.ideal * D₂.ideal :=
  rfl

end AlgebraicGeometry
