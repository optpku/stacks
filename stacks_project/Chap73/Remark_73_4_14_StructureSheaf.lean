module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.BigStructureSheaf

/-! # Global sections on the big étale site -/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Remark 73.4.14: the spaces-étale section comparison identifies sections with
functions on the corresponding algebraic space. -/
#check (AlgebraicGeometry.AlgebraicSpace.Etale.Big.spacesStructureToGamma :
  ∀ {S : Scheme.{u}} {Y : AlgebraicSpace S} (U : spacesEtaleSite Y),
    (spacesStructureSheaf Y).obj.obj (op U) ⟶
      AlgebraicGeometry.AlgebraicSpace.Etale.Big.gamma U.left)
