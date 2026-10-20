module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.SpacesHom

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.spacesRingedToposHom :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    RingedSite.ToposHom (spacesRingedSite X) (spacesRingedSite Y))
