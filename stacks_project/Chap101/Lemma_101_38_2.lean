module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.SchemeTheoreticImage.FlatCover
import StacksCheckRecall

/-!
# Scheme-theoretic images along surjective flat locally finitely presented morphisms

The scheme-theoretic image of a morphism of algebraic stacks exists if and only
if the image of its composite with a surjective, flat, locally of finite
presentation morphism exists, and in that case the two closed substacks of the
target coincide.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.38.2 (1): Let `f : X ⟶ Y` be a morphism of algebraic stacks.
Let `g : W ⟶ X` be a morphism of algebraic stacks which is surjective, flat,
and locally of finite presentation. Then the scheme-theoretic image of `f`
exists if and only if the scheme-theoretic image of `g ≫ f` exists. -/
@[stacks 0CMJ] #check (AlgebraicGeometry.AlgebraicStack.hasSchemeTheoreticImage_comp_iff :
  ∀ {S : Scheme.{u}}
    {W X Y : GroupoidsOver S}
    [AlgebraicStack W] [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) (g : W ⟶ X)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g],
    HasSchemeTheoreticImage f ↔ HasSchemeTheoreticImage (g ≫ f))

/- Lemma 101.38.2 (2): Let `f : X ⟶ Y` be a morphism of algebraic stacks.
Let `g : W ⟶ X` be a morphism of algebraic stacks which is surjective, flat,
and locally of finite presentation. If the scheme-theoretic images exist,
then these scheme-theoretic images are the same. -/
@[stacks 0CMJ] #check (AlgebraicGeometry.AlgebraicStack.schemeTheoreticImage_comp_objectProperty_eq :
  ∀ {S : Scheme.{u}}
    {W X Y : GroupoidsOver S}
    [AlgebraicStack W] [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) (g : W ⟶ X)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    {Z Z' : GroupoidsOver S} [AlgebraicStack Z] [AlgebraicStack Z']
    {toImage : X ⟶ Z} {toImage' : W ⟶ Z'} {ι : Z ⟶ Y} {ι' : Z' ⟶ Y}
    [IsSchemeTheoreticImage f toImage ι]
    [IsSchemeTheoreticImage (g ≫ f) toImage' ι'],
    (toFunctor ι).essImage = (toFunctor ι').essImage)

/- Factorization through a closed immersion descends along a surjective, flat,
locally finitely presented morphism. -/
#check (AlgebraicGeometry.AlgebraicStack.factorsThrough_comp_iff :
  ∀ {S : Scheme.{u}} {W X Y : GroupoidsOver S}
    [AlgebraicStack W] [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) (g : W ⟶ X)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    {Z : GroupoidsOver S} [AlgebraicStack Z] (ι : Z ⟶ Y)
    [Groupoids.Hom.ClosedImmersion ι],
    (∃ toZ : X ⟶ Z, Nonempty (toZ ≫ ι ≅ f)) ↔
      (∃ toZ : W ⟶ Z, Nonempty (toZ ≫ ι ≅ g ≫ f)))

/- A scheme-theoretic image factorization is preserved by precomposition with
a surjective, flat, locally finitely presented morphism. -/
#check (AlgebraicGeometry.AlgebraicStack.IsSchemeTheoreticImage.of_comp :
  ∀ {S : Scheme.{u}} {W X Y Z : GroupoidsOver S}
    [AlgebraicStack W] [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : W ⟶ X) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    [IsSchemeTheoreticImage f toImage ι],
    IsSchemeTheoreticImage (g ≫ f) (g ≫ toImage) ι)

end AlgebraicGeometry.AlgebraicStack
