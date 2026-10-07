module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import stacks_project.Chap67.Definition_67_9_2_Closed

/-!
# Base change of universally closed morphisms of algebraic spaces

Universally closed morphisms of algebraic spaces are stable under arbitrary
base change. This module records the morphism-level pullback companions for the
existing `UniversallyClosed` class from Definition 67.9.2.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace UniversallyClosed

/-- Universally closed morphisms of algebraic spaces are stable under pullback
along an arbitrary morphism, expressed by an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : UniversallyClosed g) :
    UniversallyClosed g' := sorry

end UniversallyClosed

/-- Typeclass form of the book projection `Z ×_Y X ⟶ Z`: the chosen
`pullback.snd` of a universally closed morphism is universally closed. -/
instance universallyClosed_pullback_snd {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
    [UniversallyClosed f] [HasPullback f g] :
    UniversallyClosed (pullback.snd f g) := sorry

end AlgebraicGeometry.AlgebraicSpace
