module

public import stacks_project.Chap66.Definition_66_19_2_EtaleNeighborhood
public import Mathlib.CategoryTheory.Filtered.Basic

open CategoryTheory AlgebraicGeometry

universe u

@[expose] public section

namespace AlgebraicGeometry.AlgebraicSpace.GeometricPoint.EtaleNeighborhood

/-- The category of étale neighborhoods of a geometric point of an algebraic space is
cofiltered. -/
instance instIsCofiltered {S : Scheme.{u}} {X : AlgebraicSpace S} (xbar : GeometricPoint X) :
    IsCofiltered (EtaleNeighborhood xbar) := sorry

end AlgebraicGeometry.AlgebraicSpace.GeometricPoint.EtaleNeighborhood
