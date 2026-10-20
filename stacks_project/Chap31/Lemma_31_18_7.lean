/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Relative.Flatness
import StacksCheckRecall

/-!
# Lemma 31.18.7

Flatness across a relative effective Cartier divisor.

@stack 062W
-/

@[expose] public section

/- Lemma 31.18.7: flatness away from a relative effective Cartier divisor implies flatness. -/
@[stacks 062W] #check
  (AlgebraicGeometry.IsRelativeEffectiveCartierDivisor.flat_of_flatAt_outside_support :
    ∀ {X S : AlgebraicGeometry.Scheme} (f : X ⟶ S) (D : X.IdealSheafData)
      [AlgebraicGeometry.IsRelativeEffectiveCartierDivisor f D],
      (∀ x : X, x ∉ D.support → AlgebraicGeometry.Scheme.Hom.flatAt f x) →
        AlgebraicGeometry.Flat f)
