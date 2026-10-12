/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Lemma_101_38_2_SchemeTheoreticImage
public import stacks_project.Chap101.Lemma_101_25_5_Surjective
public import stacks_project.Chap101.Lemma_101_25_5_Flat
public import stacks_project.Chap106.Lemma_106_10_1_LocallyOfFinitePresentation

/-!
# Scheme-theoretic images along surjective flat locally finitely presented morphisms

The scheme-theoretic image of a morphism of algebraic stacks exists if and only
if the image of its composite with a surjective, flat, locally of finite
presentation morphism exists, and in that case the two closed substacks of the
target coincide.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.38.2 (1): Let `f : X ⟶ Y` be a morphism of algebraic stacks.
Let `g : W ⟶ X` be a morphism of algebraic stacks which is surjective, flat,
and locally of finite presentation. Then the scheme-theoretic image of `f`
exists if and only if the scheme-theoretic image of `g ≫ f` exists. -/
@[stacks 0CMJ]
theorem hasSchemeTheoreticImage_comp_iff {S : Scheme.{u}}
    {W X Y : GroupoidsOver S}
    [AlgebraicStack W] [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) (g : W ⟶ X)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g] :
    HasSchemeTheoreticImage f ↔ HasSchemeTheoreticImage (g ≫ f) :=
  sorry

/-- Lemma 101.38.2 (2): Let `f : X ⟶ Y` be a morphism of algebraic stacks.
Let `g : W ⟶ X` be a morphism of algebraic stacks which is surjective, flat,
and locally of finite presentation. If the scheme-theoretic images exist,
then these scheme-theoretic images are the same. -/
@[stacks 0CMJ]
theorem schemeTheoreticImage_comp_objectProperty_eq {S : Scheme.{u}}
    {W X Y : GroupoidsOver S}
    [AlgebraicStack W] [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) (g : W ⟶ X)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    {Z Z' : ClosedSubstack Y} {toImage : X ⟶ Z.Y} {toImage' : W ⟶ Z'.Y}
    [IsSchemeTheoreticImage f toImage Z.ι]
    [IsSchemeTheoreticImage (g ≫ f) toImage' Z'.ι] :
    Z.objectProperty = Z'.objectProperty :=
  sorry

/-- Along a surjective, flat, locally of finite presentation morphism `g`, a
morphism `f` factors through a closed substack if and only if `g ≫ f` does. -/
theorem factorsThrough_comp_iff {S : Scheme.{u}} {W X Y : GroupoidsOver S}
    [AlgebraicStack W] [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) (g : W ⟶ X)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    (Z : ClosedSubstack Y) :
    factorsThrough f Z ↔ factorsThrough (g ≫ f) Z :=
  sorry

namespace IsSchemeTheoreticImage

/-- A scheme-theoretic image of `f` remains a scheme-theoretic image of
`g ≫ f` when `g` is surjective, flat, and locally of finite presentation. -/
theorem of_comp {S : Scheme.{u}} {W X Y Z : GroupoidsOver S}
    [AlgebraicStack W] [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : W ⟶ X) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    [IsSchemeTheoreticImage f toImage ι] :
    IsSchemeTheoreticImage (g ≫ f) (g ≫ toImage) ι :=
  sorry

end IsSchemeTheoreticImage

end AlgebraicGeometry.AlgebraicStack
