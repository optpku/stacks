module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.AffineSections
import StacksCheckRecall

/-!
# Surjectivity of structure maps of thickenings on affine spaces-étale objects

On an affine object of `X_spaces,étale`, the comparison
`closedStructureSheaf_structureMap i` of a thickening `i : X ⟶ X'` is
surjective on sections.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Thickening

/- Lemma 76.9.4: Let `S` be a scheme. Let `i : X ⟶ X'` be a thickening of
algebraic spaces over `S`. Let `U` be an affine object of `X_spaces,étale`.
Then `((closedStructureSheaf_structureMap i).hom.app (op U)).hom` is
surjective, where `𝒪_{X'}` is viewed on `X_spaces,étale` as
`closedStructureSheaf i` via 76.9.1.2 / `closedRingedToposHom`. -/
@[stacks 05ZQ]
#check (AlgebraicGeometry.AlgebraicSpace.Thickening.closedStructureSheaf_structureMap_app_surjective :
    ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} (i : X ⟶ X') [IsThickening i]
      (U : spacesEtaleSite X) [IsAffine U.left],
      Function.Surjective ((closedStructureSheaf_structureMap i).hom.app (op U)).hom)

end AlgebraicGeometry.AlgebraicSpace.Thickening
