module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.AffineLocalization

@[expose] public section

open CategoryTheory

universe u

#check (AlgebraicGeometry.AlgebraicSpace.affineEtaleLocalizationEquiv :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    {Y : AlgebraicGeometry.AlgebraicSpace S} {U : CategoryTheory.Over S}
    [AlgebraicGeometry.IsAffine U.left]
    (f : AlgebraicGeometry.AlgebraicSpace.ofOver U ⟶ Y)
    [AlgebraicGeometry.AlgebraicSpace.Etale f],
    AlgebraicGeometry.AlgebraicSpace.affineEtaleSite
        (AlgebraicGeometry.AlgebraicSpace.ofOver U) ≌
      CategoryTheory.Over (AlgebraicGeometry.AlgebraicSpace.affineEtaleSite.mk f))
