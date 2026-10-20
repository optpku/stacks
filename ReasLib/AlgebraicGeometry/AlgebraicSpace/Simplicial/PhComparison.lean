/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.TopologyComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Ph.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Ph.Comparison

/-! # Ph comparison for simplicial étale topoi -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.SimplicialObject
open scoped Simplicial MorphismOfTopoiIn

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} (U : SimplicialObject (AlgebraicSpace S))

/-- The total étale inclusion is continuous for the ph total topology. -/
instance toSliceTotal_isContinuous_ph :
    (toSliceTotal U).IsContinuous (spacesEtaleTotalTopology U)
      (sliceTotalTopology (phTopology S) U) :=
  toSliceTotal_isContinuous_topology (phTopology S) PhComparison.etale_le_ph U

/-- Inverse image along the total ph comparison preserves finite limits. -/
instance toSliceTotal_sheafPullback_preservesFiniteLimits_ph :
    PreservesFiniteLimits
      ((toSliceTotal U).sheafPullback (Type (u + 1))
        (spacesEtaleTotalTopology U) (sliceTotalTopology (phTopology S) U)) :=
  toSliceTotal_sheafPullback_preservesFiniteLimits_topology (phTopology S) PhComparison.etale_le_ph U

/-- The canonical comparison from the total ph topos to the total étale topos. -/
def phEtaleComparison :
    MorphismOfTopoiIn (spacesEtaleTotalTopology U) (sliceTotalTopology (phTopology S) U) :=
  topologyEtaleComparison (phTopology S) PhComparison.etale_le_ph U

/-- The total ph comparison inverse image is sheaf pullback along the stagewise inclusion. -/
theorem phEtaleComparison_inverseImage :
    (phEtaleComparison U)⁻¹ =
      (toSliceTotal U).sheafPullback (Type (u + 1))
        (spacesEtaleTotalTopology U) (sliceTotalTopology (phTopology S) U) := rfl

variable (X : AlgebraicSpace S)

/-- The spaces-étale inclusion is continuous for the big ph slice topology. -/
instance spacesEtaleToBig_isContinuous_ph :
    (Etale.SmallToBig.spacesEtaleToBig X).IsContinuous
      (spacesEtaleTopology X) (bigPhSite X) :=
  spacesEtaleToBig_isContinuous_topology (phTopology S) PhComparison.etale_le_ph X

/-- Inverse image of the big ph comparison preserves finite limits. -/
instance spacesEtaleToBig_sheafPullback_preservesFiniteLimits_ph :
    PreservesFiniteLimits
      ((Etale.SmallToBig.spacesEtaleToBig X).sheafPullback (Type (u + 1))
        (spacesEtaleTopology X) (bigPhSite X)) :=
  spacesEtaleToBig_sheafPullback_preservesFiniteLimits_topology (phTopology S) PhComparison.etale_le_ph X

/-- The canonical comparison from the big ph slice topos to the spaces-étale topos. -/
def spacesPhComparison : MorphismOfTopoiIn (spacesEtaleTopology X) (bigPhSite X) :=
  spacesTopologyComparison (phTopology S) PhComparison.etale_le_ph X

/-- Inverse image of the big ph comparison is sheaf pullback along the étale inclusion. -/
theorem spacesPhComparison_inverseImage :
    (spacesPhComparison X)⁻¹ =
      (Etale.SmallToBig.spacesEtaleToBig X).sheafPullback (Type (u + 1))
        (spacesEtaleTopology X) (bigPhSite X) := rfl

/-- The ph comparison factors through the big étale topos and change of topology. -/
def spacesPhComparison_inverseImage_compIso :
    (spacesPhComparison X)⁻¹ ≅
      ((Etale.SmallToBig.spacesEtaleToBig X).morphismOfTopoiInOfContinuous.{u + 1, u + 1, u + 1, u + 1, u + 1}
          (spacesEtaleTopology X) (overEtaleTopology X))⁻¹ ⋙
        (PhComparison.epsilon X)⁻¹ :=
  (Functor.sheafPullbackComp' (spacesEtaleTopology X) (overEtaleTopology X)
      (bigPhSite X) (Etale.SmallToBig.spacesEtaleToBig X) (𝟭 (Over X))
      (Functor.rightUnitor (Etale.SmallToBig.spacesEtaleToBig X))).symm

variable {X : AlgebraicSpace S} (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X)

/-- The total ph augmentation is induced by postcomposition along every augmentation component. -/
def phAugmentation : MorphismOfTopoiIn (bigPhSite X) (sliceTotalTopology (phTopology S) U) :=
  sliceAugmentationTopos (phTopology S) U a

/-- Total ph augmentation inverse image is sheafified restriction along postcomposition. -/
theorem phAugmentation_eq :
    (phAugmentation U a)⁻¹ =
      (sliceForget U a).sheafPullbackCocontinuous (Type (u + 1))
        (sliceTotalTopology (phTopology S) U) (bigPhSite X) := rfl

/-- The total ph-to-étale comparisons commute with the genuine total augmentations. -/
def phEtaleAugmentationInverseImageIso (X : AlgebraicSpace S)
    (U : SimplicialObject (AlgebraicSpace S))
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) :
    (spacesEtaleAugmentation U a)⁻¹ ⋙ (phEtaleComparison U)⁻¹ ≅
      (spacesPhComparison X)⁻¹ ⋙ (phAugmentation U a)⁻¹ :=
  topologyEtaleCommSq (phTopology S) PhComparison.etale_le_ph U a

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
