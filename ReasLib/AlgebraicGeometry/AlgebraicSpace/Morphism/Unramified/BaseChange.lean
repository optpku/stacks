/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleLocal.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.BaseChange

/-!
# Base change of unramified morphisms of algebraic spaces

Unramified morphisms of algebraic spaces are stable under arbitrary base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Unramified morphisms of algebraic spaces are stable under arbitrary base change. -/
instance unramified_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@Unramified S : MorphismProperty (AlgebraicSpace S)) := sorry

namespace Unramified

/-- Unramified morphisms of algebraic spaces are stable under pullback along an
arbitrary morphism, expressed by an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : Unramified g) : Unramified g' := sorry

/-- The base-change projection `pullback.snd f g` of an unramified morphism
`f : X ⟶ Y` is unramified. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : Unramified f) (g : Z ⟶ Y) [HasPullback f g] :
    Unramified (pullback.snd f g) := sorry

end Unramified

/-- The second projection from the pullback of an unramified morphism is unramified. -/
instance unramified_pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [Unramified f] [HasPullback f g] :
    Unramified (pullback.snd f g) := sorry

end AlgebraicGeometry.AlgebraicSpace
