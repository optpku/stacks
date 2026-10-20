module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper.BaseChange

/-!
# Base change of proper morphisms of algebraic spaces

Proper morphisms of algebraic spaces are stable under arbitrary base change.
The arbitrary-square and canonical-projection formulations express properness
of the base-changed morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.Proper.of_isPullback :
  ∀ {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : Proper g), Proper g')

#check (AlgebraicGeometry.AlgebraicSpace.Proper.pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : Proper f) (g : Z ⟶ Y) [HasPullback f g],
    Proper (pullback.snd f g))

#check (AlgebraicGeometry.AlgebraicSpace.proper_pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [Proper f] [HasPullback f g],
    Proper (pullback.snd f g))

end AlgebraicGeometry.AlgebraicSpace
