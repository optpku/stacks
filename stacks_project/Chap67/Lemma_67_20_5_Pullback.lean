module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine.BaseChange

/-!
# Base change of affine morphisms of algebraic spaces

Affine morphisms of algebraic spaces are stable under arbitrary base change.
This module records the morphism-level pullback companions for the existing
`Affine` class from Definition 67.20.2.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- The shared affine base-change API remains available through these typed checks. -/
#check (AlgebraicGeometry.AlgebraicSpace.Affine.of_isPullback :
  ∀ {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X},
    IsPullback f' g' g f → Affine g → Affine g')

#check (AlgebraicGeometry.AlgebraicSpace.Affine.pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y},
    Affine f → ∀ (g : Z ⟶ Y) [HasPullback f g], Affine (pullback.snd f g))

#check (AlgebraicGeometry.AlgebraicSpace.affine_pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [Affine f] [HasPullback f g],
    Affine (pullback.snd f g))

end AlgebraicGeometry.AlgebraicSpace
