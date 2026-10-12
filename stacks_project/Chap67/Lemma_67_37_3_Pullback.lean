/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import stacks_project.Chap67.Lemma_67_37_4_Smooth

/-!
# Base change of smooth morphisms of algebraic spaces

Smooth morphisms of algebraic spaces are stable under arbitrary base change.
This module records the morphism-level pullback companions for the existing
`Smooth` class from Definition 67.37.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Smooth

/-- Smooth morphisms of algebraic spaces are stable under pullback along an
arbitrary morphism, expressed by an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : Smooth g) : Smooth g' := sorry

/-- The base-change projection `pullback.snd f g` of a smooth morphism
`f : X ⟶ Y` is smooth. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : Smooth f) (g : Z ⟶ Y) [HasPullback f g] :
    Smooth (pullback.snd f g) := sorry

end Smooth

/-- Typeclass form of base-change stability for a smooth morphism along a
morphism for which the pullback exists. -/
instance smooth_pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [Smooth f] [HasPullback f g] :
    Smooth (pullback.snd f g) := sorry

end AlgebraicGeometry.AlgebraicSpace
