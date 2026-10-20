/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier.Relative.BaseChange
import StacksCheckRecall

/-!
# Lemma 71.9.1

Base change of relative effective Cartier divisors on algebraic spaces.

@stack 0EPN
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

universe u

/- Lemma 71.9.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. Let `D ⊂ X` be a closed subspace. Assume `D` is an effective
Cartier divisor, and `D ⟶ Y` is a flat morphism. Then for every morphism of
schemes `g : Y' ⟶ Y` the inverse image `(g')⁻¹D` along the projection
`g' : X' ⟶ X` of `X' = Y' ×_Y X` is an effective Cartier divisor on `X'`.
The closed subspace is represented by its inclusion `i : D ⟶ X`; effective
Cartier-ness supplies that this inclusion is a closed immersion. -/
@[stacks 0EPN] #check
  (AlgebraicGeometry.AlgebraicSpace.IsRelativeEffectiveCartierDivisor.isEffectiveCartierDivisor_inverseImage_pullback_fst :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      {D : AlgebraicSpace S} (i : D ⟶ X)
      [IsRelativeEffectiveCartierDivisor f i] {Y' : Over S} (g : ofOver Y' ⟶ Y),
      IsEffectiveCartierDivisor (inverseImageι (pullback.fst f g) i))

#check
  (AlgebraicGeometry.AlgebraicSpace.IsRelativeEffectiveCartierDivisor.inverseImage_pullback_fst :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      {D : AlgebraicSpace S} (i : D ⟶ X)
      [IsRelativeEffectiveCartierDivisor f i] {Y' : Over S} (g : ofOver Y' ⟶ Y),
      IsRelativeEffectiveCartierDivisor (pullback.snd f g)
        (inverseImageι (pullback.fst f g) i))
