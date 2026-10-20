module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.FiniteAbove

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AlgebraicSpace.forallAffineEtaleFiniteAbove :
  {S : Scheme.{u}} → (X : AlgebraicSpace S) →
    AlgebraicGeometry.AlgebraicSpace.Points X → Prop)
