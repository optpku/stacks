module

public import ReasLib.AlgebraicGeometry.ChowMotive.Duality
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

/- Lemma 45.4.9
If `X` is a smooth projective equidimensional `k`-scheme of dimension `d`, then
`h(X)(d)` is a left dual of `h(X)` in Chow motives: the diagonal class induces an
`ExactPairing` of `ChowMotive.h X` with `ChowMotive.tateTwist X d`. -/
@[stacks 0FGI]
#check (ChowMotive.exactPairing :
  ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
    [AlgebraicGeometry.Smooth X.hom] [AlgebraicGeometry.Projective X.hom]
    [TopologicalSpace.EquidimensionalSpace X.left] (d : ℕ),
    topologicalKrullDim X.left = (d : WithBot ℕ∞) →
      CategoryTheory.ExactPairing (ChowMotive.h X) (ChowMotive.tateTwist X d))
