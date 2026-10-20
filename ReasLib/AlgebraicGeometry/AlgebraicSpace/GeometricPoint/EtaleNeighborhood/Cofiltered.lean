module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.EtaleNeighborhood
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme
public import Mathlib.CategoryTheory.Filtered.Basic

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GeometricPoint.EtaleNeighborhood

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
  (xbar : AlgebraicGeometry.AlgebraicSpace.GeometricPoint X)

/-- The category of étale neighborhoods of a geometric point of an algebraic space is
cofiltered. -/
instance instIsCofiltered : IsCofiltered (EtaleNeighborhood xbar) := sorry

/-- Every étale neighborhood of a geometric point of an algebraic space is refined by one whose
underlying algebraic space is a scheme. -/
theorem exists_isScheme {S : Scheme.{u}} {X : AlgebraicSpace S} {xbar : GeometricPoint X}
    (U : EtaleNeighborhood xbar) :
    ∃ (U' : EtaleNeighborhood xbar) (_ : U' ⟶ U), IsScheme U'.space := sorry

end AlgebraicGeometry.AlgebraicSpace.GeometricPoint.EtaleNeighborhood
