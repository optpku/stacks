/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Immersion
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom

/-!
# Scheme-theoretic images of morphisms of algebraic stacks

A scheme-theoretic image is a least closed-immersion factorization, with
factorization and comparison squares interpreted up to 2-isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Bicategory
open CategoryTheory.FiberedCategoryOver.Groupoids
open AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

namespace AlgebraicGeometry.AlgebraicStack

/-- A scheme-theoretic image factorization presents a full and faithful closed
immersion through which a morphism factors up to 2-isomorphism, least among
such factorizations by compatible comparisons over the target. -/
class IsSchemeTheoreticImage {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y) : Prop where
  /-- The composite is 2-isomorphic to the original morphism. -/
  fac : Nonempty (toImage ≫ ι ≅ f)
  /-- The inclusion is a closed immersion. -/
  isClosedImmersion : ClosedImmersion ι
  /-- The underlying total functor of the inclusion is full. -/
  full : (toFunctor ι).Full
  /-- The underlying total functor of the inclusion is faithful. -/
  faithful : (toFunctor ι).Faithful
  /-- Every full and faithful closed-immersion factorization admits a comparison
  over the target compatible with the given factorization map. -/
  exists_lift {Z' : GroupoidsOver S} [AlgebraicStack Z'] (toZ' : X ⟶ Z')
      (ι' : Z' ⟶ Y) (hclosed : ClosedImmersion ι')
      (hfull : (toFunctor ι').Full) (hfaithful : (toFunctor ι').Faithful)
      (hfac : Nonempty (toZ' ≫ ι' ≅ f)) :
      ∃ lift : Z ⟶ Z',
        Nonempty (lift ≫ ι' ≅ ι) ∧ Nonempty (toImage ≫ lift ≅ toZ')

namespace IsSchemeTheoreticImage

/-- A scheme-theoretic image factorization is precisely a full and faithful
closed-immersion factorization admitting compatible comparisons to every other
such factorization, up to 2-isomorphism. -/
theorem spec {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y) :
    IsSchemeTheoreticImage f toImage ι ↔
      Nonempty (toImage ≫ ι ≅ f) ∧ ClosedImmersion ι ∧
        (toFunctor ι).Full ∧ (toFunctor ι).Faithful ∧
        ∀ {Z' : GroupoidsOver S} [AlgebraicStack Z'] (toZ' : X ⟶ Z')
          (ι' : Z' ⟶ Y) (hclosed : ClosedImmersion ι')
          (hfull : (toFunctor ι').Full) (hfaithful : (toFunctor ι').Faithful),
          Nonempty (toZ' ≫ ι' ≅ f) →
            ∃ lift : Z ⟶ Z',
              Nonempty (lift ≫ ι' ≅ ι) ∧ Nonempty (toImage ≫ lift ≅ toZ') :=
  sorry

/-- A scheme-theoretic image admits a compatible comparison to any full and
faithful closed-immersion factorization of the same morphism. -/
theorem lift {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {toImage : X ⟶ Z} {ι : Z ⟶ Y}
    [IsSchemeTheoreticImage f toImage ι] {Z' : GroupoidsOver S}
    [AlgebraicStack Z'] (toZ' : X ⟶ Z') (ι' : Z' ⟶ Y)
    (hclosed : ClosedImmersion ι') (hfull : (toFunctor ι').Full)
    (hfaithful : (toFunctor ι').Faithful) (hfac : Nonempty (toZ' ≫ ι' ≅ f)) :
    ∃ lift : Z ⟶ Z',
      Nonempty (lift ≫ ι' ≅ ι) ∧ Nonempty (toImage ≫ lift ≅ toZ') :=
  sorry

/-- Comparisons from a scheme-theoretic image through a full and faithful closed
immersion are unique up to a unique 2-isomorphism over that immersion. -/
theorem lift_unique {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {toImage : X ⟶ Z} {ι : Z ⟶ Y}
    [IsSchemeTheoreticImage f toImage ι] {Z' : GroupoidsOver S}
    [AlgebraicStack Z'] {ι' : Z' ⟶ Y}
    (hclosed : ClosedImmersion ι') (hfull : (toFunctor ι').Full)
    (hfaithful : (toFunctor ι').Faithful) {lift lift' : Z ⟶ Z'}
    (hι : lift ≫ ι' ≅ ι) (hι' : lift' ≫ ι' ≅ ι) :
    ∃! α : lift ≅ lift', whiskerRightIso α ι' ≪≫ hι' = hι :=
  sorry

/-- A closed immersion of algebraic stacks is a scheme-theoretic image of
itself. -/
instance of_closedImmersion {S : Scheme.{u}} {Z Y : GroupoidsOver S}
    [AlgebraicStack Z] [AlgebraicStack Y] (ι : Z ⟶ Y)
    [ClosedImmersion ι] : IsSchemeTheoreticImage ι (𝟙 Z) ι := sorry

/-- The identity morphism of an algebraic stack is a scheme-theoretic image of
itself. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    IsSchemeTheoreticImage (𝟙 X) (𝟙 X) (𝟙 X) := sorry

/-- A full and faithful closed-immersion factorization which is least among all
such factorizations over the target is a scheme-theoretic image factorization. -/
theorem of_isLeast {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    (hfac : Nonempty (toImage ≫ ι ≅ f)) (hclosed : ClosedImmersion ι)
    (hfull : (toFunctor ι).Full) (hfaithful : (toFunctor ι).Faithful)
    (hleast : ∀ {Z' : GroupoidsOver S} [AlgebraicStack Z'] (toZ' : X ⟶ Z')
      (ι' : Z' ⟶ Y) (hclosed' : ClosedImmersion ι')
      (hfull' : (toFunctor ι').Full) (hfaithful' : (toFunctor ι').Faithful),
      Nonempty (toZ' ≫ ι' ≅ f) →
        ∃ k : Z ⟶ Z', Nonempty (k ≫ ι' ≅ ι)) :
    IsSchemeTheoreticImage f toImage ι := sorry

end IsSchemeTheoreticImage

end AlgebraicGeometry.AlgebraicStack
