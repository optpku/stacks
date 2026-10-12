/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import stacks_project.Chap87.Lemma_87_24_4_FiniteType

/-!
# Base change of finite-type morphisms of formal algebraic spaces

Finite-type morphisms and locally-of-finite-type morphisms of formal algebraic
spaces are stable under arbitrary base change. This module records the
morphism-level pullback companions for `FiniteType` and the existing
`LocallyOfFiniteType` class.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

namespace FiniteType

/-- Finite-type morphisms of formal algebraic spaces are stable under pullback
along an arbitrary morphism, expressed by an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : (Over S)ᵒᵖ ⥤ Type u}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : FiniteType g) : FiniteType g' := sorry

/-- The base-change projection `pullback.snd f g` of a finite-type morphism
`f : X ⟶ Y` is of finite type. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (hf : FiniteType f) (g : Z ⟶ Y) [HasPullback f g] :
    FiniteType (pullback.snd f g) := sorry

end FiniteType

/-- Typeclass form of base-change stability for a finite-type morphism along a
morphism for which the pullback exists. -/
instance finiteType_pullback_snd {S : Scheme.{u}}
    {X Y Z : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (g : Z ⟶ Y)
    [FiniteType f] [HasPullback f g] :
    FiniteType (pullback.snd f g) := sorry

namespace LocallyOfFiniteType

/-- Locally-of-finite-type morphisms of formal algebraic spaces are stable under
pullback along an arbitrary morphism, expressed by an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : (Over S)ᵒᵖ ⥤ Type u}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : LocallyOfFiniteType g) :
    LocallyOfFiniteType g' := sorry

/-- The base-change projection `pullback.snd f g` of a locally-of-finite-type
morphism `f : X ⟶ Y` is locally of finite type. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (hf : LocallyOfFiniteType f) (g : Z ⟶ Y) [HasPullback f g] :
    LocallyOfFiniteType (pullback.snd f g) := sorry

end LocallyOfFiniteType

/-- Typeclass form of base-change stability for a locally-of-finite-type
morphism along a morphism for which the pullback exists. -/
instance locallyOfFiniteType_pullback_snd {S : Scheme.{u}}
    {X Y Z : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (g : Z ⟶ Y)
    [LocallyOfFiniteType f] [HasPullback f g] :
    LocallyOfFiniteType (pullback.snd f g) := sorry

end AlgebraicGeometry.FormalAlgebraicSpace
