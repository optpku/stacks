module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Normalization.BaseChange

@[expose] public section

universe u

/- Lemma 33.39.9: Let `X` be a locally algebraic scheme over a field `k`, let
`K/k` be a field extension, and let `y` be a point of the base change mapping
to `x`. If the stalk at `x` is reduced and one-dimensional, the residue fields
in its normalization fiber are separable over `k`, and the stalk at `y` is
one-dimensional, then the pointwise delta invariants at `x` and `y` agree. -/
@[stacks 0C3Y]
#check (AlgebraicGeometry.SchemeOverField.Normalization.DeltaInvariant.eq_baseChange_of_separableFiberResidues :
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    (X : AlgebraicGeometry.SchemeOverField k) [AlgebraicGeometry.LocallyAlgebraic X]
    (x : X.left) [_root_.IsReduced (AlgebraicGeometry.SchemeOverField.stalkRing X x)]
    (y : (AlgebraicGeometry.FieldExtension.Over.baseChange k K X).left),
    AlgebraicGeometry.FieldExtension.Over.toSource k K X y = x →
      ringKrullDim (AlgebraicGeometry.SchemeOverField.stalkRing X x) = 1 →
      AlgebraicGeometry.SchemeOverField.Normalization.FiberResidues.separableAt X x →
      ringKrullDim (AlgebraicGeometry.SchemeOverField.stalkRing
        (AlgebraicGeometry.FieldExtension.Over.baseChange k K X) y) = 1 →
      AlgebraicGeometry.SchemeOverField.deltaInvariantAt X x =
        AlgebraicGeometry.SchemeOverField.deltaInvariantAt
          (AlgebraicGeometry.FieldExtension.Over.baseChange k K X) y)
