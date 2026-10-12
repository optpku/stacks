/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation

/-!
# Base change of finite-presentation morphisms of algebraic spaces

Finite-presentation morphisms and locally-of-finite-presentation morphisms of
algebraic spaces are stable under arbitrary base change. This module records
the morphism-level pullback companions for the existing `FinitePresentation`
and `LocallyOfFinitePresentation` classes from Definition 67.28.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace FinitePresentation

/-- Finite-presentation morphisms of algebraic spaces are stable under pullback
along an arbitrary morphism, expressed by an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : FinitePresentation g) :
    FinitePresentation g' := sorry

/-- The base-change projection `pullback.snd f g` of a finite-presentation
morphism `f : X ⟶ Y` is of finite presentation. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : FinitePresentation f) (g : Z ⟶ Y) [HasPullback f g] :
    FinitePresentation (pullback.snd f g) := sorry

end FinitePresentation

/-- Typeclass form of base-change stability for a finite-presentation morphism
along a morphism for which the pullback exists. -/
instance finitePresentation_pullback_snd {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
    [FinitePresentation f] [HasPullback f g] :
    FinitePresentation (pullback.snd f g) := sorry

namespace LocallyOfFinitePresentation

/-- Locally-of-finite-presentation morphisms of algebraic spaces are stable
under pullback along an arbitrary morphism, expressed by an `IsPullback`
square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : LocallyOfFinitePresentation g) :
    LocallyOfFinitePresentation g' := sorry

/-- The base-change projection `pullback.snd f g` of a
locally-of-finite-presentation morphism `f : X ⟶ Y` is locally of finite
presentation. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : LocallyOfFinitePresentation f) (g : Z ⟶ Y) [HasPullback f g] :
    LocallyOfFinitePresentation (pullback.snd f g) := sorry

end LocallyOfFinitePresentation

/-- Typeclass form of base-change stability for a
locally-of-finite-presentation morphism along a morphism for which the
pullback exists. -/
instance locallyOfFinitePresentation_pullback_snd {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
    [LocallyOfFinitePresentation f] [HasPullback f g] :
    LocallyOfFinitePresentation (pullback.snd f g) := sorry

end AlgebraicGeometry.AlgebraicSpace
