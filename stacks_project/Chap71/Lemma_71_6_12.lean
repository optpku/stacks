/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier.Pullback.Sum

/-!
# Lemma 71.6.12

Pullback of effective Cartier divisors on algebraic spaces preserves sums,
whenever the pullbacks of the summands are defined.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Lemma 71.6.12. Pullback of effective Cartier divisors preserves sums whenever
the pullbacks of both summands are defined. -/
@[stacks 0840] #check
  (AlgebraicGeometry.AlgebraicSpace.pullback_effectiveCartierDivisorSum :
    ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} (f : X' ⟶ X)
      (D₁ D₂ : ClosedSubspace X)
      [IsEffectiveCartierDivisor D₁.ι] [IsEffectiveCartierDivisor D₂.ι]
      (hD₁ : IsEffectiveCartierDivisor (D₁.inverseImageSubspace f).ι)
      (hD₂ : IsEffectiveCartierDivisor (D₂.inverseImageSubspace f).ι),
      IsEffectiveCartierDivisor
          ((effectiveCartierDivisorSum D₁ D₂).inverseImageSubspace f).ι ∧
        Nonempty
          (Over.mk ((effectiveCartierDivisorSum D₁ D₂).inverseImageSubspace f).ι ≅
            Over.mk (effectiveCartierDivisorSum
              (D₁.inverseImageSubspace f) (D₂.inverseImageSubspace f)).ι))

