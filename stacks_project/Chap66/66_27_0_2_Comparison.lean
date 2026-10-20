module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.RingedLocalization

@[expose] public section

open CategoryTheory

universe u

#check (AlgebraicGeometry.AlgebraicSpace.spacesEtaleLocalizationIso :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    {X Y : AlgebraicGeometry.AlgebraicSpace S} (f : X ⟶ Y) [AlgebraicGeometry.AlgebraicSpace.Etale f],
    CategoryTheory.RingedSiteMap.Iso
      (AlgebraicGeometry.AlgebraicSpace.spacesEtaleTopology X)
      (AlgebraicGeometry.AlgebraicSpace.spacesStructureSheaf X)
      ((AlgebraicGeometry.AlgebraicSpace.spacesEtaleTopology Y).over
        (AlgebraicGeometry.AlgebraicSpace.spacesEtaleSite.mk f))
      ((AlgebraicGeometry.AlgebraicSpace.spacesStructureSheaf Y).over
        (AlgebraicGeometry.AlgebraicSpace.spacesEtaleSite.mk f)))
