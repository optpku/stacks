module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Sum.Effective
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Relative

/-!
# Sums of relative effective Cartier divisors

This file owns closure of relative effective Cartier divisors under sums.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

open Scheme.IdealSheafData

/-- The sum of two relative effective Cartier divisors is a relative effective Cartier divisor. -/
theorem isRelativeEffectiveCartierDivisor_sum
    {X S : Scheme} (f : X ⟶ S) (D₁ D₂ : X.IdealSheafData)
    [IsRelativeEffectiveCartierDivisor f D₁] [IsRelativeEffectiveCartierDivisor f D₂] :
    IsRelativeEffectiveCartierDivisor f (effectiveCartierDivisorSum D₁ D₂) := sorry

namespace Scheme.IdealSheafData

/-- Relative effective Cartier divisors are closed under the canonical sum operation. -/
instance instIsRelativeEffectiveCartierDivisorSum
    {X S : Scheme} (f : X ⟶ S) (D₁ D₂ : X.IdealSheafData)
    [IsRelativeEffectiveCartierDivisor f D₁] [IsRelativeEffectiveCartierDivisor f D₂] :
    IsRelativeEffectiveCartierDivisor f (effectiveCartierDivisorSum D₁ D₂) :=
  isRelativeEffectiveCartierDivisor_sum f D₁ D₂

end Scheme.IdealSheafData

end AlgebraicGeometry
