module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Sum
import Mathlib.Tactic.CrossRefAttribute

/-!
# Differences of relative effective Cartier divisors

This file owns the relative effectivity of the divisor left after cancelling one relative
effective Cartier divisor from another.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

open Scheme.IdealSheafData

variable {X S : Scheme.{u}}

namespace IsRelativeEffectiveCartierDivisor

/-- If `D₁` and `D₂` are relative effective Cartier divisors and `D₂ = D₁ + D`,
then the effective Cartier divisor `D` is relative. -/
@[stacks 0B8V]
theorem of_eq_effectiveCartierDivisorSum
    (f : X ⟶ S) (D₁ D₂ D : X.IdealSheafData)
    [IsRelativeEffectiveCartierDivisor f D₁] [IsRelativeEffectiveCartierDivisor f D₂]
    [IsEffectiveCartierDivisor D.subschemeι]
    (hsum : D₂ = effectiveCartierDivisorSum D₁ D) :
    IsRelativeEffectiveCartierDivisor f D := sorry

end IsRelativeEffectiveCartierDivisor

/-- Under the same sum identity, the structural morphism of the difference divisor is flat. -/
theorem flat_subschemeι_of_eq_effectiveCartierDivisorSum
    (f : X ⟶ S) (D₁ D₂ D : X.IdealSheafData)
    [IsRelativeEffectiveCartierDivisor f D₁] [IsRelativeEffectiveCartierDivisor f D₂]
    [IsEffectiveCartierDivisor D.subschemeι]
    (hsum : D₂ = effectiveCartierDivisorSum D₁ D) :
    Flat (D.subschemeι ≫ f) := by
  let _ : IsRelativeEffectiveCartierDivisor f D :=
    IsRelativeEffectiveCartierDivisor.of_eq_effectiveCartierDivisorSum f D₁ D₂ D hsum
  infer_instance

end AlgebraicGeometry
