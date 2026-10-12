/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Normalization.BaseChange

@[expose] public section

universe u

/- Lemma 33.39.8: Let `X` be a locally algebraic scheme over a field `k`, let
`K/k` be a field extension, and let `y` be a point of the base change mapping
to `x`. If `X` is geometrically reduced at `x` and both stalks are
one-dimensional, then the pointwise delta invariant at `x` is at most the
pointwise delta invariant at `y`. -/
@[stacks 0C3X]
#check (AlgebraicGeometry.SchemeOverField.Normalization.DeltaInvariant.le_baseChange :
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    (X : AlgebraicGeometry.SchemeOverField k) [AlgebraicGeometry.LocallyAlgebraic X]
    (x : X.left) (y : (AlgebraicGeometry.FieldExtension.Over.baseChange k K X).left),
    AlgebraicGeometry.FieldExtension.Over.toSource k K X y = x →
      AlgebraicGeometry.SchemeOverField.geometricallyReducedAt X x →
      ringKrullDim (AlgebraicGeometry.SchemeOverField.stalkRing X x) = 1 →
      ringKrullDim (AlgebraicGeometry.SchemeOverField.stalkRing
        (AlgebraicGeometry.FieldExtension.Over.baseChange k K X) y) = 1 →
      AlgebraicGeometry.SchemeOverField.deltaInvariantAt X x ≤
        AlgebraicGeometry.SchemeOverField.deltaInvariantAt
          (AlgebraicGeometry.FieldExtension.Over.baseChange k K X) y)
