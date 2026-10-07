module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import stacks_project.Chap67.Definition_67_5_2_Surjective

/-!
# Base change of surjective morphisms of algebraic spaces

Surjective morphisms of algebraic spaces are stable under arbitrary base change.
This module records the morphism-level pullback companions for the existing
`Surjective` class from Definition 67.5.2.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Surjective

/-- Surjective morphisms of algebraic spaces are stable under pullback along an
arbitrary morphism, expressed by an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : Surjective g) : Surjective g' := sorry

/-- The base-change projection `pullback.snd f g` of a surjective morphism
`f : X ⟶ Y` is surjective. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : Surjective f) (g : Z ⟶ Y) [HasPullback f g] :
    Surjective (pullback.snd f g) := sorry

end Surjective

/-- Typeclass form of base-change stability for a surjective morphism along a
morphism for which the pullback exists. -/
instance surjective_pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [Surjective f] [HasPullback f g] :
    Surjective (pullback.snd f g) := sorry

end AlgebraicGeometry.AlgebraicSpace
