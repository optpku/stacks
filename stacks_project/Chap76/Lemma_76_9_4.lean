module

public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap76.Lemma_76_9_2_Structure
public import stacks_project.Chap76.Lemma_76_9_2_Thickening

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

/-- Lemma 76.9.4: Let `S` be a scheme. Let `i : X ⟶ X'` be a thickening of
algebraic spaces over `S`. Let `U` be an affine object of `X_spaces,étale`.
Then `((closedStructureSheaf_structureMap i).hom.app (op U)).hom` is
surjective, where `𝒪_{X'}` is viewed on `X_spaces,étale` as
`closedStructureSheaf i` via 76.9.1.2 / `closedRingedToposHom`. -/
@[stacks 05ZQ]
theorem closedStructureSheaf_structureMap_app_surjective
    {S : Scheme.{u}} {X X' : AlgebraicSpace S} (i : X ⟶ X') [IsThickening i]
    (U : spacesEtaleSite X) [IsAffine U.left] :
    Function.Surjective ((closedStructureSheaf_structureMap i).hom.app (op U)).hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Thickening
