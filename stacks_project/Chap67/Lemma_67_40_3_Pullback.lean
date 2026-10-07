module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import stacks_project.Chap67.Definition_67_40_1_Proper

/-!
# Base change of proper morphisms of algebraic spaces

Proper morphisms of algebraic spaces are stable under arbitrary base change.
This module records the morphism-level pullback companions for the existing
`Proper` class from Definition 67.40.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Proper

/-- Proper morphisms of algebraic spaces are stable under pullback along an
arbitrary morphism, expressed by an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : Proper g) : Proper g' := sorry

/-- The base-change projection `pullback.snd f g` of a proper morphism
`f : X ⟶ Y` is proper. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : Proper f) (g : Z ⟶ Y) [HasPullback f g] :
    Proper (pullback.snd f g) := sorry

end Proper

/-- Typeclass form of base-change stability for a proper morphism along a
morphism for which the pullback exists. -/
instance proper_pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [Proper f] [HasPullback f g] :
    Proper (pullback.snd f g) := sorry

end AlgebraicGeometry.AlgebraicSpace
