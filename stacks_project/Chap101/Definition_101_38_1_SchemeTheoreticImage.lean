module

public import stacks_project.Chap100.Lemma_100_9_10_Substack

/-!
# Scheme-theoretic images of morphisms of algebraic stacks

A strictly full closed immersion `ι : Z ⟶ Y` is a scheme-theoretic image of
`f : X ⟶ Y` via `toImage : X ⟶ Z` when `f` factors through `ι` and `ι` is
least among strictly full closed immersions with that property, compared by
2-isomorphism over `Y`. Existence of such a factorization is postponed; there
is no chosen image carrier.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Bicategory
open AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

namespace AlgebraicGeometry.AlgebraicStack

/-- A strictly full closed immersion `ι : Z ⟶ Y` is a scheme-theoretic image of
`f : X ⟶ Y` through `toImage : X ⟶ Z` if `toImage ≫ ι = f` and every strictly
full closed immersion through which `f` factors admits a comparison from `Z`
over `Y` up to 2-isomorphism. -/
class IsSchemeTheoreticImage {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y) : Prop where
  /-- The given maps factor `f` through the closed substack `Z`. -/
  fac : toImage ≫ ι = f
  /-- The comparison `ι : Z ⟶ Y` is a closed immersion. -/
  isClosedImmersion : ClosedImmersion ι
  /-- The comparison `ι` presents a strictly full subcategory of `Y`. -/
  isStrictlyFull : IsStrictlyFull ι
  /-- Any other strictly full closed-immersion factorization of `f` admits a
  comparison from `Z` over `Y` up to 2-isomorphism, compatible with `toImage`. -/
  exists_lift {Z' : GroupoidsOver S} [AlgebraicStack Z'] (toZ' : X ⟶ Z')
      (ι' : Z' ⟶ Y) [ClosedImmersion ι'] [IsStrictlyFull ι']
      (hfac : toZ' ≫ ι' = f) :
      ∃ lift : Z ⟶ Z',
        Nonempty (lift ≫ ι' ≅ ι) ∧ Nonempty (toImage ≫ lift ≅ toZ')

namespace IsSchemeTheoreticImage

/-- A triple `(f, toImage, ι)` is a scheme-theoretic image factorization if and
only if it factors `f` through a strictly full closed immersion that is least
among such up to 2-isomorphism. -/
theorem spec {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y) :
    IsSchemeTheoreticImage f toImage ι ↔
      toImage ≫ ι = f ∧ ClosedImmersion ι ∧ IsStrictlyFull ι ∧
        ∀ {Z' : GroupoidsOver S} [AlgebraicStack Z'] (toZ' : X ⟶ Z')
          (ι' : Z' ⟶ Y) [ClosedImmersion ι'] [IsStrictlyFull ι'],
          toZ' ≫ ι' = f →
            ∃ lift : Z ⟶ Z',
              Nonempty (lift ≫ ι' ≅ ι) ∧ Nonempty (toImage ≫ lift ≅ toZ') :=
  sorry

/-- A scheme-theoretic image admits a comparison through any other strictly full
closed-immersion factorization of the same morphism, up to 2-isomorphism. -/
theorem lift {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {toImage : X ⟶ Z} {ι : Z ⟶ Y}
    [IsSchemeTheoreticImage f toImage ι] {Z' : GroupoidsOver S}
    [AlgebraicStack Z'] (toZ' : X ⟶ Z') (ι' : Z' ⟶ Y)
    [ClosedImmersion ι'] [IsStrictlyFull ι'] (hfac : toZ' ≫ ι' = f) :
    ∃ lift : Z ⟶ Z',
      Nonempty (lift ≫ ι' ≅ ι) ∧ Nonempty (toImage ≫ lift ≅ toZ') :=
  sorry

/-- Comparisons from a scheme-theoretic image through another strictly full
closed immersion are unique up to a unique 2-isomorphism over that immersion. -/
theorem lift_unique {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {toImage : X ⟶ Z} {ι : Z ⟶ Y}
    [IsSchemeTheoreticImage f toImage ι] {Z' : GroupoidsOver S}
    [AlgebraicStack Z'] {ι' : Z' ⟶ Y}
    [ClosedImmersion ι'] [IsStrictlyFull ι'] {lift lift' : Z ⟶ Z'}
    (hι : lift ≫ ι' ≅ ι) (hι' : lift' ≫ ι' ≅ ι) :
    ∃! α : lift ≅ lift', whiskerRightIso α ι' ≪≫ hι' = hι :=
  sorry

/-- A strictly full closed immersion of algebraic stacks is a scheme-theoretic
image of itself. -/
instance of_closedImmersion {S : Scheme.{u}} {Z Y : GroupoidsOver S}
    [AlgebraicStack Z] [AlgebraicStack Y] (ι : Z ⟶ Y)
    [ClosedImmersion ι] [IsStrictlyFull ι] :
    IsSchemeTheoreticImage ι (𝟙 Z) ι := sorry

/-- The identity morphism of an algebraic stack is a scheme-theoretic image of
itself. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    IsSchemeTheoreticImage (𝟙 X) (𝟙 X) (𝟙 X) := sorry

/-- A least closed-substack factorization of `f` is a scheme-theoretic image
factorization. -/
theorem of_isLeast_closedSubstack {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (Z : ClosedSubstack Y) (toImage : X ⟶ Z.Y) (hfac : toImage ≫ Z.ι = f)
    (hleast : ∀ Z' : ClosedSubstack Y,
      (∃ toZ' : X ⟶ Z'.Y, toZ' ≫ Z'.ι = f) →
        ∃ k : Z.Y ⟶ Z'.Y, Nonempty (k ≫ Z'.ι ≅ Z.ι)) :
    IsSchemeTheoreticImage f toImage Z.ι := sorry

/-- A scheme-theoretic image factorization is least among closed substacks of
`Y` through which `f` factors, compared over `Y` up to 2-isomorphism. -/
theorem isLeast_closedSubstack {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {toImage : X ⟶ Z} {ι : Z ⟶ Y}
    [IsSchemeTheoreticImage f toImage ι] (Z' : ClosedSubstack Y)
    (hfac : ∃ toZ' : X ⟶ Z'.Y, toZ' ≫ Z'.ι = f) :
    ∃ k : Z ⟶ Z'.Y, Nonempty (k ≫ Z'.ι ≅ ι) := sorry

/-- The closed substack of `Y` presented by a scheme-theoretic image
factorization. -/
def toClosedSubstack {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [h : IsSchemeTheoreticImage f toImage ι] : ClosedSubstack Y where
  Y := Z
  ι := ι
  isAlgebraicStack := inferInstance
  isClosedImmersion := h.isClosedImmersion
  isStrictlyFull := h.isStrictlyFull

/-- The inclusion of `toClosedSubstack f toImage ι` is the given comparison
`ι`. -/
theorem toClosedSubstack_ι {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [IsSchemeTheoreticImage f toImage ι] :
    (toClosedSubstack f toImage ι).ι = ι := sorry

end IsSchemeTheoreticImage

end AlgebraicGeometry.AlgebraicStack
