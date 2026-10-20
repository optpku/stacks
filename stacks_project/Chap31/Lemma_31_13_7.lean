module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Sum.Effective
import StacksCheckRecall

/-!
# Lemma 31.13.7

The sum of effective Cartier divisors is effective Cartier.

@stack 01WU
-/

@[expose] public section

/- Lemma 31.13.7: The sum of two effective Cartier divisors is an effective Cartier divisor. -/
@[stacks 01WU] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.isEffectiveCartierDivisor_sum :
    ∀ {X : AlgebraicGeometry.Scheme} (D₁ D₂ : X.IdealSheafData)
      [AlgebraicGeometry.IsEffectiveCartierDivisor D₁.subschemeι]
      [AlgebraicGeometry.IsEffectiveCartierDivisor D₂.subschemeι],
      AlgebraicGeometry.IsEffectiveCartierDivisor
        (AlgebraicGeometry.effectiveCartierDivisorSum D₁ D₂).subschemeι)
