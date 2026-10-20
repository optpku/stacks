module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Stalk.Spaces

open CategoryTheory AlgebraicGeometry Opposite

universe u

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/- The colimit of sections over all algebraic-space étale neighborhoods of a geometric point. -/
#check (AlgebraicGeometry.AlgebraicSpace.GeometricPoint.spacesEtaleStalk :
  (xbar : AlgebraicSpace.GeometricPoint X) →
    ((AlgebraicSpace.spacesEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) → Type (u + 1))

/- The germ of a section at an algebraic-space étale neighborhood. -/
#check (AlgebraicGeometry.AlgebraicSpace.GeometricPoint.toSpacesEtaleStalk :
  ∀ {xbar : AlgebraicSpace.GeometricPoint X}
    {F' : (AlgebraicSpace.spacesEtaleSite X)ᵒᵖ ⥤ Type (u + 1)}
    (U : AlgebraicSpace.GeometricPoint.EtaleNeighborhood xbar),
    F'.obj (op U.toSpacesEtale) →
      AlgebraicSpace.GeometricPoint.spacesEtaleStalk xbar F')
