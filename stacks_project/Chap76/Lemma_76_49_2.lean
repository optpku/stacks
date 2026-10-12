/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_49_2_BaseLocus

/-!
# Where a morphism of algebraic spaces is unramified and universally injective

In a commutative triangle of algebraic spaces `X ⟶ Y` over `Z` with
`X ⟶ Z` locally of finite type and closed, and with `X ×_Y X ⟶ Z` closed,
a test map into `Z` factors through the unramified-and-universally-injective
base locus if and only if the base-changed map `X_{Z'} ⟶ Y_{Z'}` is
unramified and universally injective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.UnramifiedUniversallyInjective

/-- Lemma 76.49.2: Consider a commutative triangle of algebraic spaces over `S`
given by `f : X ⟶ Y` and `q : Y ⟶ Z`. Assume that `p = f ≫ q` is locally of
finite type and closed, and that `p₂ = selfFiberToBase f q` is closed. Then a
morphism `g : Z' ⟶ Z` factors through the open subspace
`baseLocus f q ⊂ Z` if and only if the base change
`overBaseChange f q g : X_{Z'} ⟶ Y_{Z'}` is unramified and
universally injective. -/
@[stacks 05X9]
theorem exists_lift_iff_overBaseChange {S : Scheme.{u}}
    {X Y Z Z' : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z) (g : Z' ⟶ Z)
    [LocallyOfFiniteType (f ≫ q)] [Closed (f ≫ q)]
    [Closed (selfFiberToBase f q)] :
    (∃ ℓ : Z' ⟶ (baseLocus f q).X, ℓ ≫ (baseLocus f q).ι = g) ↔
      Unramified (overBaseChange f q g) ∧
        UniversallyInjective (overBaseChange f q g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.UnramifiedUniversallyInjective
