module

import StacksCheckRecall
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Nodal.Etale

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Lemma 53.19.13: an étale morphism to a one-dimensional locally algebraic scheme over a
field preserves and reflects whether corresponding points are closed and nodal. -/
@[stacks 0C57] #check
  (AlgebraicGeometry.SchemeOverField.closedPointAndNode_iff_of_etale :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [LocallyAlgebraic X]
    (h_dimension : topologicalKrullDim X.left = 1) {Y : Scheme.{u}}
    (f : Y ⟶ X.left) [Etale f] (x : X.left) (y : Y) (hy : f y = x),
    (x ∈ closedPoints X.left ∧ isNode X x) ↔
      (y ∈ closedPoints Y ∧ isNode (Over.mk (f ≫ X.hom)) y))

end AlgebraicGeometry.SchemeOverField
