module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Torsor.SheafCategory

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.GroupAlgebraicSpace.SheafTorsors.baseChangeGroupSheaf :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    {U : Over S} (b : AlgebraicGeometry.AlgebraicSpace.ofOver U ⟶ B),
    Sheaf (Scheme.fppfTopology.over U.left) GrpCat.{u})
