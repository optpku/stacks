/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Pullback.Sum
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 31.13.14 (1): if the pullbacks of two effective Cartier divisors are defined, then the
pullback of their sum is defined. -/
@[stacks 01WW] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.pullbackDefined_effectiveCartierDivisorSum :
    ∀ {S S' : AlgebraicGeometry.Scheme.{u}} (f : S' ⟶ S)
      (D₁ D₂ : S.IdealSheafData)
      [AlgebraicGeometry.IsEffectiveCartierDivisor D₁.subschemeι]
      [AlgebraicGeometry.IsEffectiveCartierDivisor D₂.subschemeι],
      AlgebraicGeometry.Scheme.IdealSheafData.pullbackDefined D₁ f →
        AlgebraicGeometry.Scheme.IdealSheafData.pullbackDefined D₂ f →
          AlgebraicGeometry.Scheme.IdealSheafData.pullbackDefined
            (AlgebraicGeometry.effectiveCartierDivisorSum D₁ D₂) f)

/- Lemma 31.13.14 (2): the pullback of the sum of two effective Cartier divisors with defined
pullbacks is the sum of their pullbacks. -/
@[stacks 01WW] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.comap_effectiveCartierDivisorSum_of_pullbackDefined :
    ∀ {S S' : AlgebraicGeometry.Scheme.{u}} (f : S' ⟶ S)
      (D₁ D₂ : S.IdealSheafData)
      [AlgebraicGeometry.IsEffectiveCartierDivisor D₁.subschemeι]
      [AlgebraicGeometry.IsEffectiveCartierDivisor D₂.subschemeι],
      AlgebraicGeometry.Scheme.IdealSheafData.pullbackDefined D₁ f →
        AlgebraicGeometry.Scheme.IdealSheafData.pullbackDefined D₂ f →
          (AlgebraicGeometry.effectiveCartierDivisorSum D₁ D₂).comap f =
            AlgebraicGeometry.effectiveCartierDivisorSum (D₁.comap f) (D₂.comap f))
