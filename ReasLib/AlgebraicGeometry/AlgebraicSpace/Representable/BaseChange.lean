/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Property

/-!
# Base change of transferred morphism properties of algebraic spaces

If a morphism property of algebraic spaces is stable under base change, then
so is its transfer to morphisms of presheaves representable by algebraic
spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace relativeAlgebraicSpaces

/-- A morphism property of algebraic spaces stable under base change transfers
to a morphism property of presheaves stable under base change. -/
instance isStableUnderBaseChange {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)} [P.IsStableUnderBaseChange] :
    (relativeAlgebraicSpaces P).IsStableUnderBaseChange := sorry

/-- Morphisms of presheaves satisfying `relativeAlgebraicSpaces P` are stable
under pullback along an arbitrary morphism, expressed by an `IsPullback`
square, when `P` is stable under base change. -/
theorem of_isPullback {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)} [P.IsStableUnderBaseChange]
    {F G G' Fg : (Over S)ᵒᵖ ⥤ Type u} {a : F ⟶ G} {g : G' ⟶ G}
    {a' : Fg ⟶ G'} {f : Fg ⟶ F} (sq : IsPullback f a' a g)
    (ha : relativeAlgebraicSpaces P a) :
    relativeAlgebraicSpaces P a' := sorry

/-- The base-change projection `pullback.fst g a` of a morphism of presheaves
satisfying `relativeAlgebraicSpaces P` again satisfies
`relativeAlgebraicSpaces P`, when `P` is stable under base change. -/
theorem pullback_fst {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)} [P.IsStableUnderBaseChange]
    {F G G' : (Over S)ᵒᵖ ⥤ Type u} {a : F ⟶ G} {g : G' ⟶ G}
    [HasPullback g a] (ha : relativeAlgebraicSpaces P a) :
    relativeAlgebraicSpaces P (pullback.fst g a) := sorry

end relativeAlgebraicSpaces

end AlgebraicGeometry.AlgebraicSpace
