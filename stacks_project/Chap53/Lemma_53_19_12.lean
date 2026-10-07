module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Nodal.BaseChange

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Lemma 53.19.12: for a point `y` of the scalar extension of a one-dimensional locally
algebraic `k`-scheme `X`, with image `x` in `X`, the point `x` is closed and a node if and
only if `y` is closed and a node. -/
@[stacks 0C56] #check
  (AlgebraicGeometry.SchemeOverField.closedPointAndNode_iff_baseChange :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    (X : SchemeOverField k) [LocallyAlgebraic X]
    (h_dimension : topologicalKrullDim X.left = 1)
    (x : X.left) (y : (FieldExtension.Over.baseChange k K X).left)
    (hy : FieldExtension.Over.toSource k K X y = x),
    (x ∈ closedPoints X.left ∧ isNode X x) ↔
      (y ∈ closedPoints (FieldExtension.Over.baseChange k K X).left ∧
        isNode (FieldExtension.Over.baseChange k K X) y))

end AlgebraicGeometry.SchemeOverField
