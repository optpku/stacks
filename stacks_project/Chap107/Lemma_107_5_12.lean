module

public import ReasLib.AlgebraicGeometry.Scheme.Dimension.Local
import StacksCheckRecall

@[expose] public section

universe u

open AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme

/- Lemma 107.5.12: if `X` is a finite-dimensional scheme of dimension `d`, then there exists a
closed (and hence finite type) point `x ∈ X` such that `topologicalKrullDimAt x = d`. -/
@[stacks 0DRR] #check
  (AlgebraicGeometry.Scheme.exists_closedPoint_topologicalKrullDimAt_eq :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) {d : ℕ}, topologicalKrullDim X = d →
      ∃ x : X, x ∈ closedPoints X ∧ AlgebraicGeometry.IsFiniteTypePoint x ∧
        topologicalKrullDimAt x = d)

end AlgebraicGeometry.Scheme
