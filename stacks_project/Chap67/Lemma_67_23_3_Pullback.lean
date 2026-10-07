module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import stacks_project.Chap67.Definition_67_40_1_FiniteType

/-!
# Base change of finite-type morphisms of algebraic spaces

Finite-type morphisms and locally-of-finite-type morphisms of algebraic spaces
are stable under arbitrary base change. This module records the morphism-level
pullback companions for the existing `FiniteType` and `LocallyOfFiniteType`
classes from Definition 67.23.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace FiniteType

/-- Finite-type morphisms of algebraic spaces are stable under pullback along an
arbitrary morphism, expressed by an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : FiniteType g) : FiniteType g' := sorry

/-- The base-change projection `pullback.snd f g` of a finite-type morphism
`f : X ⟶ Y` is of finite type. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : FiniteType f) (g : Z ⟶ Y) [HasPullback f g] :
    FiniteType (pullback.snd f g) := sorry

end FiniteType

/-- Typeclass form of base-change stability for a finite-type morphism along a
morphism for which the pullback exists. -/
instance finiteType_pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [FiniteType f] [HasPullback f g] :
    FiniteType (pullback.snd f g) := sorry

namespace LocallyOfFiniteType

/-- Locally-of-finite-type morphisms of algebraic spaces are stable under
pullback along an arbitrary morphism, expressed by an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : LocallyOfFiniteType g) :
    LocallyOfFiniteType g' := sorry

/-- The base-change projection `pullback.snd f g` of a locally-of-finite-type
morphism `f : X ⟶ Y` is locally of finite type. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : LocallyOfFiniteType f) (g : Z ⟶ Y) [HasPullback f g] :
    LocallyOfFiniteType (pullback.snd f g) := sorry

end LocallyOfFiniteType

/-- Typeclass form of base-change stability for a locally-of-finite-type
morphism along a morphism for which the pullback exists. -/
instance locallyOfFiniteType_pullback_snd {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
    [LocallyOfFiniteType f] [HasPullback f g] :
    LocallyOfFiniteType (pullback.snd f g) := sorry

end AlgebraicGeometry.AlgebraicSpace
