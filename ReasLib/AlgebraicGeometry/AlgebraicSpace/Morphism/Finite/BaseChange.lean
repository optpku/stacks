/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Base change of integral and finite morphisms of algebraic spaces

Integral and finite morphisms of algebraic spaces are preserved by arbitrary
pullback.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An integral morphism remains integral in any pullback square. -/
theorem isIntegralHom_of_isPullback {S : Scheme.{u}}
    {X Y Y' B : AlgebraicSpace S} {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y}
    {g' : Y' ⟶ X} (sq : IsPullback f' g' g f) (hg : IsIntegralHom g) :
    IsIntegralHom g' :=
  sorry

namespace IsIntegralHom

/-- The second projection from a pullback of an integral morphism is integral. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : IsIntegralHom f) (g : Z ⟶ Y) [HasPullback f g] :
    IsIntegralHom (pullback.snd f g) :=
  sorry

end IsIntegralHom

/-- The second projection from a pullback of an integral morphism is integral
when the source morphism is available as an instance. -/
instance isIntegralHom_pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [IsIntegralHom f] [HasPullback f g] :
    IsIntegralHom (pullback.snd f g) :=
  sorry

/-- Integral morphisms are stable under arbitrary base change. -/
instance isIntegralHom_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@IsIntegralHom S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

/-- A finite morphism remains finite in any pullback square. -/
theorem isFinite_of_isPullback {S : Scheme.{u}}
    {X Y Y' B : AlgebraicSpace S} {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y}
    {g' : Y' ⟶ X} (sq : IsPullback f' g' g f) (hg : IsFinite g) : IsFinite g' :=
  sorry

namespace IsFinite

/-- The second projection from a pullback of a finite morphism is finite. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : IsFinite f) (g : Z ⟶ Y) [HasPullback f g] :
    IsFinite (pullback.snd f g) :=
  sorry

end IsFinite

/-- The second projection from a pullback of a finite morphism is finite when
the source morphism is available as an instance. -/
instance isFinite_pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [IsFinite f] [HasPullback f g] :
    IsFinite (pullback.snd f g) :=
  sorry

/-- Finite morphisms are stable under arbitrary base change. -/
instance isFinite_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@IsFinite S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
