/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Perfect

/-!
# Flat base change of perfect morphisms of algebraic spaces

Perfect morphisms of algebraic spaces are preserved by base change
along a flat morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Perfect

/-- Perfect morphisms of algebraic spaces are stable under base change
along a flat morphism. -/
instance instIsStableUnderBaseChangeAgainst {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChangeAgainst
      (@Perfect S : MorphismProperty (AlgebraicSpace S))
      (@Flat S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- Perfect morphisms of algebraic spaces are stable under base change
along a fixed flat morphism. -/
instance instIsStableUnderBaseChangeAlong {S : Scheme.{u}}
    {Y' Y : AlgebraicSpace S} (g : Y' ⟶ Y) [Flat g] :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@Perfect S : MorphismProperty (AlgebraicSpace S)) g := sorry

/-- The pullback of a perfect morphism of algebraic spaces along a
flat morphism, expressed by an `IsPullback` square, is perfect. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X} [Flat f]
    (sq : IsPullback f' g' g f) (hg : Perfect g) : Perfect g' := sorry

/-- The base-change projection `pullback.snd f g` of a perfect morphism
`f : X ⟶ Y` along a flat morphism `g` is perfect. -/
instance pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g] [Perfect f] [Flat g] :
    Perfect (pullback.snd f g) := sorry

end AlgebraicGeometry.AlgebraicSpace.Perfect
