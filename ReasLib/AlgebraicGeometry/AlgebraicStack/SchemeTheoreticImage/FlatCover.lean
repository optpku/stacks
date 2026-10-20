/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.SchemeTheoreticImage.Existence
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation

/-!
# Scheme-theoretic images under flat covers

Precomposing with a surjective, flat, locally finitely presented morphism
preserves and reflects existence of scheme-theoretic images and preserves
their essential-image object properties.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism factors through a closed immersion up to 2-isomorphism if and
only if its composite with a surjective, flat, locally finitely presented
morphism does. -/
theorem factorsThrough_comp_iff {S : Scheme.{u}} {W X Y : GroupoidsOver S}
    [AlgebraicStack W] [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) (g : W ⟶ X)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    {Z : GroupoidsOver S} [AlgebraicStack Z] (ι : Z ⟶ Y)
    [Groupoids.Hom.ClosedImmersion ι] :
    (∃ toZ : X ⟶ Z, Nonempty (toZ ≫ ι ≅ f)) ↔
      (∃ toZ : W ⟶ Z, Nonempty (toZ ≫ ι ≅ g ≫ f)) :=
  sorry

namespace IsSchemeTheoreticImage

/-- A scheme-theoretic image factorization remains a scheme-theoretic image
after precomposition with a surjective, flat, locally finitely presented
morphism. -/
instance of_comp {S : Scheme.{u}} {W X Y Z : GroupoidsOver S}
    [AlgebraicStack W] [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : W ⟶ X) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    [IsSchemeTheoreticImage f toImage ι] :
    IsSchemeTheoreticImage (g ≫ f) (g ≫ toImage) ι :=
  sorry

end IsSchemeTheoreticImage

/-- A morphism of algebraic stacks has a scheme-theoretic image if and only
if its composite with a surjective, flat, locally finitely presented morphism
has one. -/
theorem hasSchemeTheoreticImage_comp_iff {S : Scheme.{u}}
    {W X Y : GroupoidsOver S}
    [AlgebraicStack W] [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) (g : W ⟶ X)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g] :
    HasSchemeTheoreticImage f ↔ HasSchemeTheoreticImage (g ≫ f) :=
  sorry

/-- Scheme-theoretic images of a morphism and its composite with a surjective,
flat, locally finitely presented morphism have the same essential-image
object property in the target. -/
theorem schemeTheoreticImage_comp_objectProperty_eq {S : Scheme.{u}}
    {W X Y : GroupoidsOver S}
    [AlgebraicStack W] [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) (g : W ⟶ X)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    {Z Z' : GroupoidsOver S} [AlgebraicStack Z] [AlgebraicStack Z']
    {toImage : X ⟶ Z} {toImage' : W ⟶ Z'} {ι : Z ⟶ Y} {ι' : Z' ⟶ Y}
    [IsSchemeTheoreticImage f toImage ι]
    [IsSchemeTheoreticImage (g ≫ f) toImage' ι'] :
    (toFunctor ι).essImage = (toFunctor ι').essImage :=
  sorry

end AlgebraicGeometry.AlgebraicStack
