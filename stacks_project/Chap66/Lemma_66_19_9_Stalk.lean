module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.InverseImage.Stalk

/-! # Stalks of small étale inverse image -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint

universe u

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
variable (xbar : GeometricPoint X)
variable (G : Sheaf (smallEtaleTopology Y) (Type (u + 1)))

/- Lemma 66.19.9 (4): inverse image preserves stalks at the corresponding geometric points. -/
#check (AlgebraicGeometry.AlgebraicSpace.smallEtaleInverseImage_stalkIso f xbar G :
  (toSmallEtalePoint xbar).sheafFiber.obj
      ((smallEtaleMorphismOfTopoi f).inverseImage.obj G) ≅
    (toSmallEtalePoint (xbar.map f)).sheafFiber.obj G)
