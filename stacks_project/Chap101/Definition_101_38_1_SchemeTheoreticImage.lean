/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.SchemeTheoreticImage
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
open CategoryTheory.FiberedCategoryOver.Groupoids
open AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

namespace AlgebraicGeometry.AlgebraicStack

namespace IsSchemeTheoreticImage

/-- A least closed-substack factorization of `f` is a scheme-theoretic image
factorization. -/
theorem of_isLeast_closedSubstack {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (Z : ClosedSubstack Y) (toImage : X ⟶ Z.Y) (hfac : Nonempty (toImage ≫ Z.ι ≅ f))
    (hleast : ∀ Z' : ClosedSubstack Y,
      (∃ toZ' : X ⟶ Z'.Y, Nonempty (toZ' ≫ Z'.ι ≅ f)) →
        ∃ k : Z.Y ⟶ Z'.Y, Nonempty (k ≫ Z'.ι ≅ Z.ι)) :
    IsSchemeTheoreticImage f toImage Z.ι := by
  apply of_isLeast f toImage Z.ι hfac Z.isClosedImmersion
    Z.isStrictlyFull.full Z.isStrictlyFull.faithful
  intro Z' hZ' toZ' ι' hclosed hfull hfaithful hfac'
  exact hleast
    { Y := Z'
      ι := ι'
      isAlgebraicStack := hZ'
      isClosedImmersion := hclosed
      isStrictlyFull := { full := hfull, faithful := hfaithful } }
    ⟨toZ', hfac'⟩

/-- A scheme-theoretic image factorization is least among closed substacks of
`Y` through which `f` factors, compared over `Y` up to 2-isomorphism. -/
theorem isLeast_closedSubstack {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {toImage : X ⟶ Z} {ι : Z ⟶ Y}
    [IsSchemeTheoreticImage f toImage ι] (Z' : ClosedSubstack Y)
    (hfac : ∃ toZ' : X ⟶ Z'.Y, Nonempty (toZ' ≫ Z'.ι ≅ f)) :
    ∃ k : Z ⟶ Z'.Y, Nonempty (k ≫ Z'.ι ≅ ι) := by
  obtain ⟨toZ', hfac'⟩ := hfac
  obtain ⟨k, hk, hcompat⟩ : ∃ k : Z ⟶ Z'.Y,
      Nonempty (k ≫ Z'.ι ≅ ι) ∧ Nonempty (toImage ≫ k ≅ toZ') :=
    lift toZ' Z'.ι Z'.isClosedImmersion
      Z'.isStrictlyFull.full Z'.isStrictlyFull.faithful hfac'
  exact ⟨k, hk⟩

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
  isStrictlyFull := { full := h.full, faithful := h.faithful }

/-- The inclusion of `toClosedSubstack f toImage ι` is the given comparison
`ι`. -/
theorem toClosedSubstack_ι {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [IsSchemeTheoreticImage f toImage ι] :
    (toClosedSubstack f toImage ι).ι = ι := rfl

end IsSchemeTheoreticImage

end AlgebraicGeometry.AlgebraicStack
