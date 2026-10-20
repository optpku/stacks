module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.EtaleNeighborhood.Cofiltered
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

@[expose] public section

/- Lemma 66.19.3: the category of étale neighborhoods of a geometric point of an algebraic
space is cofiltered. -/
@[stacks 04JW] #check
  (AlgebraicGeometry.AlgebraicSpace.GeometricPoint.EtaleNeighborhood.instIsCofiltered :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      (xbar : AlgebraicSpace.GeometricPoint X),
      IsCofiltered (AlgebraicSpace.GeometricPoint.EtaleNeighborhood xbar))
