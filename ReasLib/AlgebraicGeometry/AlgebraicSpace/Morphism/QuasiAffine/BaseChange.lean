/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.QuasiAffine
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Base change of quasi-affine morphisms of algebraic spaces

Quasi-affine morphisms of algebraic spaces are stable under arbitrary base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QuasiAffine

/-- In a pullback square, the base change of a quasi-affine morphism of algebraic
spaces is quasi-affine. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : QuasiAffine g) : QuasiAffine g' := sorry

/-- The second projection from a pullback of a quasi-affine morphism of algebraic
spaces is quasi-affine. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : QuasiAffine f) (g : Z ⟶ Y) [HasPullback f g] :
    QuasiAffine (pullback.snd f g) := sorry

/-- The second projection from a pullback of a quasi-affine morphism is
quasi-affine whenever the pullback exists. -/
instance instPullbackSnd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [QuasiAffine f] [HasPullback f g] :
    QuasiAffine (pullback.snd f g) := sorry

/-- Quasi-affine morphisms of algebraic spaces are stable under arbitrary base change. -/
instance stableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@QuasiAffine S : MorphismProperty (AlgebraicSpace S)) := sorry

end AlgebraicGeometry.AlgebraicSpace.QuasiAffine
