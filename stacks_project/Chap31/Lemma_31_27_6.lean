/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Picard
import StacksCheckRecall

/-!
# Lemma 31.27.6

The Picard-to-Weil-class-group comparison is injective on a normal scheme.

@stack 0BE8
-/

@[expose] public section

universe u

/- Lemma 31.27.6 -/
@[stacks 0BE8] #check
  (@AlgebraicGeometry.Scheme.injective_picardToWeilDivisorClassGroup :
    ∀ (X : AlgebraicGeometry.Scheme.{u})
      [AlgebraicGeometry.IsLocallyNoetherian X] [AlgebraicGeometry.IsIntegral X],
      X.isNormal → Function.Injective
        (AlgebraicGeometry.Scheme.picardToWeilDivisorClassGroup X))
