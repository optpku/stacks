module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Relative.Difference
import StacksCheckRecall

/-!
# Lemma 31.18.4

Differences of relative effective Cartier divisors.

@stack 0B8V
-/

@[expose] public section

open CategoryTheory

universe u

/- Lemma 31.18.4: a residual effective Cartier divisor between relative effective Cartier
divisors is relative. -/
@[stacks 0B8V] #check (AlgebraicGeometry.IsRelativeEffectiveCartierDivisor.of_eq_effectiveCartierDivisorSum :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      (D₁ D₂ D : X.IdealSheafData)
      [AlgebraicGeometry.IsRelativeEffectiveCartierDivisor f D₁]
      [AlgebraicGeometry.IsRelativeEffectiveCartierDivisor f D₂]
      [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι],
      D₂ = AlgebraicGeometry.effectiveCartierDivisorSum D₁ D →
        AlgebraicGeometry.IsRelativeEffectiveCartierDivisor f D)
#check @AlgebraicGeometry.flat_subschemeι_of_eq_effectiveCartierDivisorSum
