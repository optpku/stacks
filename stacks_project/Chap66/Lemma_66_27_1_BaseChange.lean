module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.PullbackLift

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.spacesEtalePullbackLift :
  ∀ {S : Scheme.{u}} {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y)
    [Etale p] [Etale q] (hcomm : p ≫ f = g ≫ q),
    spacesEtaleSite.mk p ⟶ (spacesEtalePullback f).obj (spacesEtaleSite.mk q))
