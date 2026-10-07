module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import stacks_project.Chap67.Definition_67_46_2_FiniteLocallyFree

/-!
# Base change of finite locally free morphisms of algebraic spaces

Finite locally free morphisms of algebraic spaces are stable under arbitrary
base change. This module records the morphism-level pullback companions for the
existing `FiniteLocallyFree` class from Definition 67.46.2.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace FiniteLocallyFree

/-- Finite locally free morphisms of algebraic spaces are stable under pullback
along an arbitrary morphism, expressed by an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : FiniteLocallyFree g) :
    FiniteLocallyFree g' := sorry

/-- The base-change projection `pullback.snd f g` of a finite locally free
morphism `f : X ⟶ Y` is finite locally free. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : FiniteLocallyFree f) (g : Z ⟶ Y) [HasPullback f g] :
    FiniteLocallyFree (pullback.snd f g) := sorry

end FiniteLocallyFree

/-- Typeclass form of base-change stability for a finite locally free morphism
along a morphism for which the pullback exists. -/
instance finiteLocallyFree_pullback_snd {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
    [FiniteLocallyFree f] [HasPullback f g] :
    FiniteLocallyFree (pullback.snd f g) := sorry

end AlgebraicGeometry.AlgebraicSpace
