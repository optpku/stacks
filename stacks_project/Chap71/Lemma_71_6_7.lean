/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier.Sum.Effective
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Lemma 71.6.7
The sum of two effective Cartier divisors is an effective Cartier divisor.
-/
@[stacks 083V] #check
  (AlgebraicGeometry.AlgebraicSpace.isEffectiveCartierDivisor_sum :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (D₁ D₂ : ClosedSubspace X)
      [IsEffectiveCartierDivisor D₁.ι] [IsEffectiveCartierDivisor D₂.ι],
      IsEffectiveCartierDivisor (effectiveCartierDivisorSum D₁ D₂).ι)
