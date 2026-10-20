module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.CodimensionZero
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 66.11.2: the codimension-zero points of an algebraic space are dense
in its canonical topological space of points. -/
@[stacks 0BAR] #check
  (AlgebraicGeometry.AlgebraicSpace.dense_setOf_localRingDimAt_eq_zero :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
      Dense (setOf fun x : AlgebraicGeometry.AlgebraicSpace.Points X ↦
        AlgebraicGeometry.AlgebraicSpace.localRingDimAt x = 0))
