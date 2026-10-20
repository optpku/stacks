module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.AffineEtale

open CategoryTheory

universe u

#check (AlgebraicGeometry.AlgebraicSpace.AffineEtale.commStructurePresheaf :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
    (AlgebraicGeometry.AlgebraicSpace.affineEtaleSite X)ᵒᵖ ⥤ CommRingCat.{u})
