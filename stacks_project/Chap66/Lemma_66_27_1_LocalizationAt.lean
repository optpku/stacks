module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.SpacesLocalization

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.spacesRingedHom.localizationAt :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (V : spacesEtaleSite Y) {U : spacesEtaleSite X}
    (c : U ⟶ (spacesEtalePullback f).obj V),
    RingedSite.ToposHom
      ((spacesRingedSite X).localization U) ((spacesRingedSite Y).localization V))
