/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Pullback

/-!
# Base change of surjective morphisms of algebraic spaces

Surjective morphisms of algebraic spaces are stable under arbitrary base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Surjective morphisms of algebraic spaces are stable under base change. -/
instance surjective_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@Surjective S : MorphismProperty (AlgebraicSpace S)) := sorry

namespace Surjective

/-- Surjective morphisms of algebraic spaces are stable under pullback along an
arbitrary morphism, expressed by an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : Surjective g) : Surjective g' :=
  MorphismProperty.of_isPullback sq hg

/-- The base-change projection `pullback.snd f g` of a surjective morphism
`f : X ⟶ Y` is surjective. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : Surjective f) (g : Z ⟶ Y) [HasPullback f g] :
    Surjective (pullback.snd f g) :=
  MorphismProperty.pullback_snd _ _ hf

end Surjective

/-- The second projection of a pullback of a surjective morphism is surjective. -/
instance surjective_pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [Surjective f] [HasPullback f g] :
    Surjective (pullback.snd f g) :=
  Surjective.pullback_snd inferInstance g

end AlgebraicGeometry.AlgebraicSpace
