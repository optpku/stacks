/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_49_5_BaseLocus

/-!
# Where a morphism of algebraic spaces is surjective and flat

In a commutative triangle of algebraic spaces `X ⟶ Y` over `Z` with
`X ⟶ Z` locally of finite presentation, flat, and closed, and `Y ⟶ Z`
locally of finite type and closed, a test map into `Z` factors through
the surjective-and-flat base locus if and only if the base-changed map
`X_{Z'} ⟶ Y_{Z'}` is surjective and flat.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.SurjectiveFlat

/-- Lemma 76.49.5: Consider a commutative triangle of algebraic spaces over `S`
given by `f : X ⟶ Y` and `q : Y ⟶ Z`. Assume that `p = f ≫ q` is locally of
finite presentation, flat, and closed, and that `q` is locally of finite type
and closed. Then a morphism `g : Z' ⟶ Z` factors through the open subspace
`baseLocus f q ⊂ Z` if and only if the base change
`overBaseChange f q g : X_{Z'} ⟶ Y_{Z'}` is surjective and flat. -/
@[stacks 05XC]
theorem exists_lift_iff_overBaseChange {S : Scheme.{u}}
    {X Y Z Z' : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z) (g : Z' ⟶ Z)
    [LocallyOfFinitePresentation (f ≫ q)] [Flat (f ≫ q)]
    [Closed (f ≫ q)] [LocallyOfFiniteType q] [Closed q] :
    (∃ ℓ : Z' ⟶ (baseLocus f q).X, ℓ ≫ (baseLocus f q).ι = g) ↔
      Surjective (overBaseChange f q g) ∧ Flat (overBaseChange f q g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.SurjectiveFlat
