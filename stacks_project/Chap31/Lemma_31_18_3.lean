/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Relative.Sum
import StacksCheckRecall

/-!
# Lemma 31.18.3

Sums of relative effective Cartier divisors.

@stack 0B8U
-/

@[expose] public section

open CategoryTheory

universe u

/- Lemma 31.18.3: the sum of two relative effective Cartier divisors on `X` over `S` is again
a relative effective Cartier divisor on `X` over `S`. -/
@[stacks 0B8U] #check
  (AlgebraicGeometry.isRelativeEffectiveCartierDivisor_sum :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      (D₁ D₂ : X.IdealSheafData)
      [AlgebraicGeometry.IsRelativeEffectiveCartierDivisor f D₁]
      [AlgebraicGeometry.IsRelativeEffectiveCartierDivisor f D₂],
      AlgebraicGeometry.IsRelativeEffectiveCartierDivisor f
        (AlgebraicGeometry.effectiveCartierDivisorSum D₁ D₂))
