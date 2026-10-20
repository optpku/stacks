/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Base change of smooth morphisms of algebraic spaces

Smooth morphisms of algebraic spaces are stable under arbitrary base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Smooth morphisms of algebraic spaces are stable under base change. -/
instance smooth_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@Smooth S : MorphismProperty (AlgebraicSpace S)) := sorry

namespace Smooth

/-- Smooth morphisms of algebraic spaces are stable under pullback along an
arbitrary morphism, expressed by an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : Smooth g) : Smooth g' :=
  MorphismProperty.of_isPullback sq hg

/-- The base-change projection `pullback.snd f g` of a smooth morphism
`f : X ⟶ Y` is smooth. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : Smooth f) (g : Z ⟶ Y) [HasPullback f g] :
    Smooth (pullback.snd f g) :=
  MorphismProperty.pullback_snd _ _ hf

end Smooth

/-- The second projection of a pullback of a smooth morphism is smooth. -/
instance smooth_pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [Smooth f] [HasPullback f g] :
    Smooth (pullback.snd f g) :=
  Smooth.pullback_snd inferInstance g

end AlgebraicGeometry.AlgebraicSpace
