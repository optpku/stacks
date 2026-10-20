/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.TopologyComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FppfEtale.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fppf.Comparison

/-! # Fppf comparison for simplicial étale topoi -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.SimplicialObject
open scoped Simplicial MorphismOfTopoiIn

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} (U : SimplicialObject (AlgebraicSpace S))

/-- The total étale inclusion is continuous for the fppf total topology. -/
instance toSliceTotal_isContinuous :
    (toSliceTotal U).IsContinuous (spacesEtaleTotalTopology U)
      (sliceTotalTopology (fppfTopology S) U) :=
  toSliceTotal_isContinuous_topology (fppfTopology S) FppfEtale.etale_le_fppf U

/-- Inverse image along the total fppf comparison preserves finite limits. -/
instance toSliceTotal_sheafPullback_preservesFiniteLimits :
    PreservesFiniteLimits
      ((toSliceTotal U).sheafPullback (Type (u + 1))
        (spacesEtaleTotalTopology U) (sliceTotalTopology (fppfTopology S) U)) :=
  toSliceTotal_sheafPullback_preservesFiniteLimits_topology (fppfTopology S) FppfEtale.etale_le_fppf U

/-- The total étale inclusion is an exact morphism to the fppf total site. -/
instance toSliceTotal_isExactMorphismOfSites :
    IsExactMorphismOfSites.{u + 1, u + 1, u + 1, u + 1, u + 1}
      (spacesEtaleTotalTopology U) (sliceTotalTopology (fppfTopology S) U) (toSliceTotal U) where
  toIsContinuous := toSliceTotal_isContinuous U
  preservesFiniteLimits_sheafPullback := toSliceTotal_sheafPullback_preservesFiniteLimits U

/-- The canonical comparison from the total fppf topos to the total étale topos. -/
def fppfEtaleComparison :
    MorphismOfTopoiIn (spacesEtaleTotalTopology U) (sliceTotalTopology (fppfTopology S) U) :=
  topologyEtaleComparison (fppfTopology S) FppfEtale.etale_le_fppf U

/-- The total fppf comparison inverse image is sheaf pullback along the stagewise inclusion. -/
theorem fppfEtaleComparison_inverseImage :
    (fppfEtaleComparison U)⁻¹ =
      (toSliceTotal U).sheafPullback (Type (u + 1))
        (spacesEtaleTotalTopology U) (sliceTotalTopology (fppfTopology S) U) := rfl

variable (X : AlgebraicSpace S)

/-- The spaces-étale inclusion is continuous for the big fppf slice topology. -/
instance spacesEtaleToBig_isContinuous_fppf :
    (Etale.SmallToBig.spacesEtaleToBig X).IsContinuous
      (spacesEtaleTopology X) (overFppfTopology X) :=
  spacesEtaleToBig_isContinuous_topology (fppfTopology S) FppfEtale.etale_le_fppf X

/-- Inverse image of the big fppf comparison preserves finite limits. -/
instance spacesEtaleToBig_sheafPullback_preservesFiniteLimits_fppf :
    PreservesFiniteLimits
      ((Etale.SmallToBig.spacesEtaleToBig X).sheafPullback (Type (u + 1))
        (spacesEtaleTopology X) (overFppfTopology X)) :=
  spacesEtaleToBig_sheafPullback_preservesFiniteLimits_topology (fppfTopology S) FppfEtale.etale_le_fppf X

/-- The spaces-étale inclusion is an exact morphism to the big fppf slice site. -/
instance spacesEtaleToBig_isExactMorphismOfSites_fppf :
    IsExactMorphismOfSites.{u + 1, u + 1, u + 1, u + 1, u + 1}
      (spacesEtaleTopology X) (overFppfTopology X) (Etale.SmallToBig.spacesEtaleToBig X) where
  toIsContinuous := spacesEtaleToBig_isContinuous_fppf X
  preservesFiniteLimits_sheafPullback := spacesEtaleToBig_sheafPullback_preservesFiniteLimits_fppf X

/-- The canonical comparison from the big fppf slice topos to the spaces-étale topos. -/
def spacesFppfComparison : MorphismOfTopoiIn (spacesEtaleTopology X) (overFppfTopology X) :=
  spacesTopologyComparison (fppfTopology S) FppfEtale.etale_le_fppf X

/-- Inverse image of the big fppf comparison is sheaf pullback along the étale inclusion. -/
theorem spacesFppfComparison_inverseImage :
    (spacesFppfComparison X)⁻¹ =
      (Etale.SmallToBig.spacesEtaleToBig X).sheafPullback (Type (u + 1))
        (spacesEtaleTopology X) (overFppfTopology X) := rfl

/-- The spaces-to-big inclusion restricts to the small-to-big inclusion. -/
theorem spacesFppfComparison_comp_small :
    smallEtaleToSpaces X ⋙ Etale.SmallToBig.spacesEtaleToBig X =
      Etale.SmallToBig.smallEtaleToBig X := rfl

variable {X : AlgebraicSpace S} (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X)

/-- Degree-zero étale pullback followed by the total inclusion is continuous for the fppf total topology. -/
instance augmentationFunctor_comp_toSliceTotal_isContinuous :
    (augmentationFunctor U a ⋙ toSliceTotal U).IsContinuous
      (spacesEtaleTopology X) (sliceTotalTopology (fppfTopology S) U) :=
  Functor.isContinuous_comp (augmentationFunctor U a) (toSliceTotal U)
    (spacesEtaleTopology X) (spacesEtaleTotalTopology U)
    (sliceTotalTopology (fppfTopology S) U)

/-- The spaces-étale inclusion followed by degree-zero augmentation pullback is continuous for the fppf total topology. -/
instance spacesEtaleToBig_comp_sliceAugmentationPullback_isContinuous :
    (Etale.SmallToBig.spacesEtaleToBig X ⋙ sliceAugmentationPullback U a).IsContinuous
      (spacesEtaleTopology X) (sliceTotalTopology (fppfTopology S) U) :=
  Functor.isContinuous_comp (Etale.SmallToBig.spacesEtaleToBig X)
    (sliceAugmentationPullback U a) (spacesEtaleTopology X) (overFppfTopology X)
    (sliceTotalTopology (fppfTopology S) U)

/-- The total fppf augmentation is induced by postcomposition along every augmentation component. -/
def fppfAugmentation : MorphismOfTopoiIn (overFppfTopology X) (sliceTotalTopology (fppfTopology S) U) :=
  sliceAugmentationTopos (fppfTopology S) U a

/-- Total fppf augmentation inverse image is sheafified restriction along postcomposition. -/
theorem fppfAugmentation_eq :
    (fppfAugmentation U a)⁻¹ =
      (sliceForget U a).sheafPullbackCocontinuous (Type (u + 1))
        (sliceTotalTopology (fppfTopology S) U) (overFppfTopology X) := rfl

/-- The total fppf-to-étale comparisons commute with the genuine total augmentations. -/
def fppfEtaleCommSq :
    (spacesEtaleAugmentation U a)⁻¹ ⋙ (fppfEtaleComparison U)⁻¹ ≅
      (spacesFppfComparison X)⁻¹ ⋙ (fppfAugmentation U a)⁻¹ :=
  topologyEtaleCommSq (fppfTopology S) FppfEtale.etale_le_fppf U a

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
