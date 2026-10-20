/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType

/-!
# Base change of finite-type morphisms of algebraic spaces

Finite-type morphisms and locally-of-finite-type morphisms of algebraic spaces
are stable under arbitrary base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The base change of a finite-type morphism of algebraic spaces is of finite type. -/
instance finiteType_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@FiniteType S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The base change of a locally-of-finite-type morphism of algebraic spaces is
locally of finite type. -/
instance locallyOfFiniteType_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@LocallyOfFiniteType S : MorphismProperty (AlgebraicSpace S)) := sorry

namespace FiniteType

/-- Finite-type morphisms of algebraic spaces are stable under pullback along an
arbitrary morphism, expressed by an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : FiniteType g) : FiniteType g' :=
  MorphismProperty.of_isPullback sq hg

/-- The base-change projection `pullback.snd f g` of a finite-type morphism
`f : X ⟶ Y` is of finite type. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : FiniteType f) (g : Z ⟶ Y) [HasPullback f g] :
    FiniteType (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g hf

end FiniteType

/-- The pullback projection of a finite-type morphism is of finite type. -/
instance finiteType_pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [FiniteType f] [HasPullback f g] :
    FiniteType (pullback.snd f g) :=
  FiniteType.pullback_snd inferInstance g

namespace LocallyOfFiniteType

/-- Locally-of-finite-type morphisms of algebraic spaces are stable under
pullback along an arbitrary morphism, expressed by an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : LocallyOfFiniteType g) :
    LocallyOfFiniteType g' :=
  MorphismProperty.of_isPullback sq hg

/-- The base-change projection `pullback.snd f g` of a locally-of-finite-type
morphism `f : X ⟶ Y` is locally of finite type. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : LocallyOfFiniteType f) (g : Z ⟶ Y) [HasPullback f g] :
    LocallyOfFiniteType (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g hf

end LocallyOfFiniteType

/-- The pullback projection of a locally-of-finite-type morphism is locally of finite type. -/
instance locallyOfFiniteType_pullback_snd {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
    [LocallyOfFiniteType f] [HasPullback f g] :
    LocallyOfFiniteType (pullback.snd f g) :=
  LocallyOfFiniteType.pullback_snd inferInstance g

end AlgebraicGeometry.AlgebraicSpace
