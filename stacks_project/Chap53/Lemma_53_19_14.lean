module

public import stacks_project.Chap53.Lemma_53_19_7
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Nodal.Restriction
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Lemma 53.19.14: a closed point of a one-dimensional locally algebraic scheme over a
finite separable field extension is a node exactly when it is a node after restriction to
the smaller field. -/
@[stacks 0CD6] #check
  (AlgebraicGeometry.SchemeOverField.isNode_iff_restrictScalars :
    ∀ {k k' : Type u} [Field k] [Field k'] [Algebra k k'] [FiniteDimensional k k']
    [Algebra.IsSeparable k k'] (X : SchemeOverField k') [LocallyAlgebraic X]
    (h_dimension : topologicalKrullDim X.left = 1)
    (x : X.left) (h_closed : x ∈ closedPoints X.left),
    isNode X x ↔ isNode ((Over.map (FieldExtension.specMap k k')).obj X) x)

end AlgebraicGeometry.SchemeOverField
