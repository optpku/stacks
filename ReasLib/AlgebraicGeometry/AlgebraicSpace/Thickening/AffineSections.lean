module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.StructureSheaf

/-!
# Surjectivity of structure maps of thickenings on affine spaces-étale objects

The canonical structure map of a thickening is surjective on sections over
every affine object of the spaces-étale site.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Thickening

/-- For a thickening of algebraic spaces, the canonical map from the inverse-image
structure sheaf to the structure sheaf is surjective on sections over every affine
object of the spaces-étale site. -/
@[stacks 05ZQ]
theorem closedStructureSheaf_structureMap_app_surjective
    {S : Scheme.{u}} {X X' : AlgebraicSpace S} (i : X ⟶ X') [IsThickening i]
    (U : spacesEtaleSite X) [IsAffine U.left] :
    Function.Surjective ((closedStructureSheaf_structureMap i).hom.app (op U)).hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Thickening
