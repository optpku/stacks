/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import stacks_project.Chap88.Lemma_88_23_4_Proper

/-!
# Base change of proper morphisms of formal algebraic spaces

Proper morphisms of formal algebraic spaces are stable under arbitrary base
change. This module records the morphism-level pullback companions for the
existing `Proper` class from Definition 87.31.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

namespace Proper

/-- Proper morphisms of formal algebraic spaces are stable under pullback
along an arbitrary morphism, expressed by an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : (Over S)ᵒᵖ ⥤ Type u}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : Proper g) : Proper g' := sorry

/-- The base-change projection `pullback.snd f g` of a proper morphism
`f : X ⟶ Y` is proper. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (hf : Proper f) (g : Z ⟶ Y) [HasPullback f g] :
    Proper (pullback.snd f g) := sorry

end Proper

/-- Typeclass form of base-change stability for a proper morphism along a
morphism for which the pullback exists. -/
instance proper_pullback_snd {S : Scheme.{u}}
    {X Y Z : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (g : Z ⟶ Y)
    [Proper f] [HasPullback f g] :
    Proper (pullback.snd f g) := sorry

end AlgebraicGeometry.FormalAlgebraicSpace
