module

public import ReasLib.AlgebraicGeometry.SheafTorsor.Restriction

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

variable {S : Scheme.{u}}

/- Inverse image of fppf sheaves of groups along a morphism of schemes over the base. -/
#check (AlgebraicGeometry.SheafTorsors.inverseImageGrp :
  ∀ {U U' : Over S}, (U ⟶ U') →
    Sheaf (Scheme.fppfTopology.over U'.left) GrpCat.{u} ⥤
      Sheaf (Scheme.fppfTopology.over U.left) GrpCat.{u})
