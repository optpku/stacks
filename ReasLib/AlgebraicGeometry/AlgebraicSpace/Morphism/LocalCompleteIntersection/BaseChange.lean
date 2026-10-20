/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocalCompleteIntersection
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection.BaseChange

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsLocalCompleteIntersection

/-- Local complete intersection morphisms of algebraic spaces are stable under
base change along a flat morphism. -/
instance instIsStableUnderBaseChangeAgainst {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChangeAgainst
      (@IsLocalCompleteIntersection S : MorphismProperty (AlgebraicSpace S))
      (@Flat S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

/-- Local complete intersection morphisms of algebraic spaces are stable under
base change along a fixed flat morphism. -/
instance instIsStableUnderBaseChangeAlong {S : Scheme.{u}}
    {Y' Y : AlgebraicSpace S} (g : Y' ⟶ Y) [Flat g] :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsLocalCompleteIntersection S : MorphismProperty (AlgebraicSpace S)) g :=
  sorry

/-- The pullback of a local complete intersection morphism of algebraic spaces
along a flat morphism, expressed by an `IsPullback` square, is a local complete
intersection. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X} [Flat f]
    (sq : IsPullback f' g' g f) (hg : IsLocalCompleteIntersection g) :
    IsLocalCompleteIntersection g' :=
  sorry

/-- The second projection from the pullback of a local complete intersection
morphism of algebraic spaces along a flat morphism is a local complete
intersection morphism. -/
instance pullback_snd {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g]
    [IsLocalCompleteIntersection f] [Flat g] :
    IsLocalCompleteIntersection (pullback.snd f g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsLocalCompleteIntersection
