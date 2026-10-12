/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import stacks_project.Chap67.Lemma_67_30_5_Flat

/-!
# Base change of flat morphisms of algebraic spaces

Flat morphisms of algebraic spaces are stable under arbitrary base change.
This module records the morphism-level pullback companions for the existing
`Flat` class from Definition 67.30.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Flat

/-- Flat morphisms of algebraic spaces are stable under pullback along an
arbitrary morphism, expressed by an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : Flat g) : Flat g' := sorry

/-- The base-change projection `pullback.snd f g` of a flat morphism
`f : X ⟶ Y` is flat. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : Flat f) (g : Z ⟶ Y) [HasPullback f g] :
    Flat (pullback.snd f g) := sorry

end Flat

/-- Typeclass form of base-change stability for a flat morphism along a
morphism for which the pullback exists. -/
instance flat_pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [Flat f] [HasPullback f g] :
    Flat (pullback.snd f g) := sorry

end AlgebraicGeometry.AlgebraicSpace
