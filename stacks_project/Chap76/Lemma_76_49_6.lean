module

public import stacks_project.Chap76.Lemma_76_49_6_BaseLocus

/-!
# Where a morphism of algebraic spaces is an isomorphism

In a commutative triangle of algebraic spaces `X ⟶ Y` over `Z` with
`X ⟶ Z` locally of finite presentation, flat, and universally closed, and
`Y ⟶ Z` locally of finite type, closed, and separated, a test map into `Z`
factors through the isomorphism base locus if and only if the base-changed
map `X_{Z'} ⟶ Y_{Z'}` is an isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Isomorphism

/-- Lemma 76.49.6: Consider a commutative triangle of algebraic spaces over `S`
given by `f : X ⟶ Y` and `q : Y ⟶ Z`. Assume that `p = f ≫ q` is locally of
finite presentation, flat, and universally closed, and that `q` is locally of
finite type, closed, and separated. Then a morphism `g : Z' ⟶ Z` factors
through the open subspace `baseLocus f q ⊂ Z` if and only if the base change
`overBaseChange f q g : X_{Z'} ⟶ Y_{Z'}` is an isomorphism. -/
@[stacks 05XD]
theorem exists_lift_iff_overBaseChange {S : Scheme.{u}}
    {X Y Z Z' : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z) (g : Z' ⟶ Z)
    [LocallyOfFinitePresentation (f ≫ q)] [Flat (f ≫ q)]
    [UniversallyClosed (f ≫ q)] [LocallyOfFiniteType q]
    [Closed q] [Separated q] :
    (∃ ℓ : Z' ⟶ (baseLocus f q).X, ℓ ≫ (baseLocus f q).ι = g) ↔
      IsIso (overBaseChange f q g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Isomorphism
