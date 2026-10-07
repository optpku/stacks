module

public import stacks_project.Chap54.Lemma_54_16_10
public import stacks_project.Chap29.Lemma_29_43_13

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Projective

/-- Lemma 54.16.11: if `S` is Noetherian and `f : X ⟶ S` is proper with `X` regular of
topological Krull dimension `2`, then `f` is projective over `S`. -/
@[stacks 0C5P]
instance instOfProperRegularDimensionTwo
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsProper f] [Scheme.Regular X]
    [h_dim : Fact (topologicalKrullDim X = 2)] : Projective f := sorry

end AlgebraicGeometry.Projective
