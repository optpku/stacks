module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.AffineLocalization
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- 66.27.0.5: if `f : ofOver U ⟶ Y` is étale and `U.left` is affine, the affine étale
site of `ofOver U` is the localization of the affine étale site of `Y` at its chart. -/
@[stacks 04M2] #check (AlgebraicGeometry.AlgebraicSpace.affineEtaleLocalizationEquiv :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    {Y : AlgebraicGeometry.AlgebraicSpace S} {U : CategoryTheory.Over S}
    [AlgebraicGeometry.IsAffine U.left]
    (f : AlgebraicGeometry.AlgebraicSpace.ofOver U ⟶ Y)
    [AlgebraicGeometry.AlgebraicSpace.Etale f],
    AlgebraicGeometry.AlgebraicSpace.affineEtaleSite
        (AlgebraicGeometry.AlgebraicSpace.ofOver U) ≌
      CategoryTheory.Over (AlgebraicGeometry.AlgebraicSpace.affineEtaleSite.mk f))

#check (AlgebraicGeometry.AlgebraicSpace.affineEtaleLocalizationFunctor.instIsMorphismOfSites :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    {Y : AlgebraicGeometry.AlgebraicSpace S} {U : CategoryTheory.Over S}
    [AlgebraicGeometry.IsAffine U.left]
    (f : AlgebraicGeometry.AlgebraicSpace.ofOver U ⟶ Y)
    [AlgebraicGeometry.AlgebraicSpace.Etale f],
    CategoryTheory.IsMorphismOfSites
      (AlgebraicGeometry.AlgebraicSpace.affineEtaleTopology
        (AlgebraicGeometry.AlgebraicSpace.ofOver U))
      ((AlgebraicGeometry.AlgebraicSpace.affineEtaleTopology Y).over
        (AlgebraicGeometry.AlgebraicSpace.affineEtaleSite.mk f))
      (AlgebraicGeometry.AlgebraicSpace.affineEtaleLocalizationFunctor f))

#check (AlgebraicGeometry.AlgebraicSpace.affineEtaleLocalizationInverse.instIsMorphismOfSites :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    {Y : AlgebraicGeometry.AlgebraicSpace S} {U : CategoryTheory.Over S}
    [AlgebraicGeometry.IsAffine U.left]
    (f : AlgebraicGeometry.AlgebraicSpace.ofOver U ⟶ Y)
    [AlgebraicGeometry.AlgebraicSpace.Etale f],
    CategoryTheory.IsMorphismOfSites
      ((AlgebraicGeometry.AlgebraicSpace.affineEtaleTopology Y).over
        (AlgebraicGeometry.AlgebraicSpace.affineEtaleSite.mk f))
      (AlgebraicGeometry.AlgebraicSpace.affineEtaleTopology
        (AlgebraicGeometry.AlgebraicSpace.ofOver U))
      (AlgebraicGeometry.AlgebraicSpace.affineEtaleLocalizationInverse f))
