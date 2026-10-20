/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Closed.InverseImage

/-!
# Base change of relative effective Cartier divisors on algebraic spaces

An effective Cartier divisor on an algebraic space which is flat over the base
remains effective Cartier after base change along a morphism from a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsRelativeEffectiveCartierDivisor

/-- The inverse image of a relative effective Cartier divisor along the first
leg of a pullback square whose new base is a scheme is an effective Cartier
divisor. -/
theorem of_isPullback {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {D : AlgebraicSpace S} (i : D ⟶ X)
    [IsRelativeEffectiveCartierDivisor f i]
    {Y' : Over S} {X' : AlgebraicSpace S}
    {g : ofOver Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ ofOver Y'}
    (sq : IsPullback g' f' f g) :
    IsEffectiveCartierDivisor (inverseImageι g' i) :=
  sorry

/-- The inverse image of a relative effective Cartier divisor along
`pullback.fst f g`, for a morphism `g` from a scheme, is an effective Cartier
divisor. -/
theorem isEffectiveCartierDivisor_inverseImage_pullback_fst
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {D : AlgebraicSpace S} (i : D ⟶ X)
    [IsRelativeEffectiveCartierDivisor f i] {Y' : Over S}
    (g : ofOver Y' ⟶ Y) :
    IsEffectiveCartierDivisor (inverseImageι (pullback.fst f g) i) :=
  sorry

/-- After base change from a scheme, the inverse image of a relative effective
Cartier divisor remains relative effective Cartier over the new base. -/
instance inverseImage_pullback_fst {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {D : AlgebraicSpace S} (i : D ⟶ X)
    [IsRelativeEffectiveCartierDivisor f i] {Y' : Over S}
    (g : ofOver Y' ⟶ Y) :
    IsRelativeEffectiveCartierDivisor (pullback.snd f g)
      (inverseImageι (pullback.fst f g) i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsRelativeEffectiveCartierDivisor
