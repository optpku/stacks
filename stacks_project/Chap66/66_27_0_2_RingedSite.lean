module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Spaces

@[expose] public section

universe u

#check (AlgebraicGeometry.AlgebraicSpace.spacesStructureSheaf :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
    CategoryTheory.Sheaf (AlgebraicGeometry.AlgebraicSpace.spacesEtaleTopology X) RingCat.{u})
