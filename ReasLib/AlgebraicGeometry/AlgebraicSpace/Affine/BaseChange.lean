/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Base change of affine morphisms of algebraic spaces

Affine morphisms of algebraic spaces are stable under arbitrary base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Affine morphisms of algebraic spaces are stable under arbitrary base change. -/
instance affine_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@Affine S : MorphismProperty (AlgebraicSpace S)) := sorry

namespace Affine

/-- In a pullback square, the base change of an affine morphism of algebraic
spaces is affine. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : Affine g) : Affine g' := sorry

/-- The base-change projection `pullback.snd f g` of an affine morphism
`f : X ⟶ Y` is affine. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : Affine f) (g : Z ⟶ Y) [HasPullback f g] :
    Affine (pullback.snd f g) := sorry

end Affine

/-- The second projection from a pullback of an affine morphism is affine. -/
instance affine_pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [Affine f] [HasPullback f g] :
    Affine (pullback.snd f g) := sorry

end AlgebraicGeometry.AlgebraicSpace
