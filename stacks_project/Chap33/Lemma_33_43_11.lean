module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.DimensionOne
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 33.43.11: let `X` be a separated scheme of finite type over a field `k`. If
`topologicalKrullDim X.left ≤ 1` and no one-dimensional reduced irreducible component is proper
over `k`, then `X.left` is affine. -/
@[stacks 0A28] #check
  (AlgebraicGeometry.Algebraic.isAffine_of_dimLEOne_of_nonproper_irreducibleComponents :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Algebraic X] [IsSeparated X.hom],
      topologicalKrullDim X.left ≤ 1 →
        (∀ Z : irreducibleComponents X.left,
          topologicalKrullDim (X.left.irreducibleComponentSubscheme Z) = 1 →
            ¬ IsProper (X.left.irreducibleComponentSubschemeι Z ≫ X.hom)) →
          IsAffine X.left)
