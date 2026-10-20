module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.EtaleAugmentation
public import Mathlib.CategoryTheory.Yoneda

/-! # Total étale comparison with a finer topology -/

set_option backward.privateInPublic true

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.SimplicialObject
open scoped Simplicial MorphismOfTopoiIn

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} (J : GrothendieckTopology (AlgebraicSpace S))
    (hJ : etaleTopology ≤ J) (U : SimplicialObject (AlgebraicSpace S))

include hJ in
/-- The stagewise inclusion is continuous for a topology finer than the étale topology. -/
theorem toSliceTotal_isContinuous_topology :
    (toSliceTotal U).IsContinuous (spacesEtaleTotalTopology U) (sliceTotalTopology J U) :=
  sorry

/-- Sheaf pullback from the total étale site to the total slice site. -/
private def topologyEtalePullback :=
  @Functor.sheafPullback _ _ _ _ (toSliceTotal U) (Type (u + 1)) _
    (spacesEtaleTotalTopology U) (sliceTotalTopology J U)
    (toSliceTotal_isContinuous_topology J hJ U) inferInstance

/-- Total-site comparison inverse image preserves finite limits. -/
theorem toSliceTotal_sheafPullback_preservesFiniteLimits_topology :
    PreservesFiniteLimits (topologyEtalePullback J hJ U) :=
  sorry

/-- The canonical total comparison from a finer slice topology to the étale topology. -/
def topologyEtaleComparison :
    MorphismOfTopoiIn (spacesEtaleTotalTopology U) (sliceTotalTopology J U) :=
  @Functor.morphismOfTopoiInOfContinuous.{u + 1, u + 1, u + 1, u + 1, u + 1} _ _ _ _ (toSliceTotal U)
    (spacesEtaleTotalTopology U) (sliceTotalTopology J U)
    (toSliceTotal_isContinuous_topology J hJ U) inferInstance inferInstance
    (toSliceTotal_sheafPullback_preservesFiniteLimits_topology J hJ U)

variable (X : AlgebraicSpace S)

include hJ in
/-- The spaces-étale inclusion in a slice site is continuous for a finer topology. -/
theorem spacesEtaleToBig_isContinuous_topology :
    (Etale.SmallToBig.spacesEtaleToBig X).IsContinuous (spacesEtaleTopology X) (J.over X) :=
  sorry

/-- Sheaf pullback along the inclusion of a spaces-étale site in a finer slice site. -/
private def spacesTopologyPullback :=
  @Functor.sheafPullback _ _ _ _ (Etale.SmallToBig.spacesEtaleToBig X) (Type (u + 1)) _
    (spacesEtaleTopology X) (J.over X)
    (spacesEtaleToBig_isContinuous_topology J hJ X) inferInstance

/-- Spaces-étale to slice-site comparison inverse image preserves finite limits. -/
theorem spacesEtaleToBig_sheafPullback_preservesFiniteLimits_topology :
    PreservesFiniteLimits (spacesTopologyPullback J hJ X) :=
  sorry

/-- The canonical comparison from a finer big slice topos to the spaces-étale topos. -/
def spacesTopologyComparison :
    MorphismOfTopoiIn (spacesEtaleTopology X) (J.over X) :=
  @Functor.morphismOfTopoiInOfContinuous.{u + 1, u + 1, u + 1, u + 1, u + 1} _ _ _ _ (Etale.SmallToBig.spacesEtaleToBig X)
    (spacesEtaleTopology X) (J.over X)
    (spacesEtaleToBig_isContinuous_topology J hJ X) inferInstance inferInstance
    (spacesEtaleToBig_sheafPullback_preservesFiniteLimits_topology J hJ X)

/-- The étale specialization of the spaces-to-big comparison is left exact. -/
instance spacesEtaleToBig_sheafPullback_preservesFiniteLimits_etale :
    PreservesFiniteLimits
      ((Etale.SmallToBig.spacesEtaleToBig X).sheafPullback (Type (u + 1))
        (spacesEtaleTopology X) (overEtaleTopology X)) :=
  spacesEtaleToBig_sheafPullback_preservesFiniteLimits_topology etaleTopology le_rfl X

variable {X} (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X)

/-- The right adjoint obtained by first restricting a total slice sheaf to étale objects. -/
private def topologySquareEtaleRight :=
  (topologyEtaleComparison J hJ U).pushforward ⋙ (spacesEtaleAugmentation U a).pushforward

/-- The right adjoint obtained by first applying total slice augmentation. -/
private def topologySquareSliceRight :=
  (sliceAugmentationTopos J U a).pushforward ⋙ (spacesTopologyComparison J hJ X).pushforward

/-- The degree-zero cartesian object associated to an étale object over the augmentation target. -/
private def comparisonZeroObj (V : spacesEtaleSite X) : sliceTotalSite U :=
  toSliceTotalObj U (SpacesEtale.ofStage (op ⦋0⦌)
    ((spacesEtalePullback (a.app (op ⦋0⦌))).obj V))

/-- The projection from a degree-zero cartesian object to its target slice object. -/
private def comparisonZeroProjection (V : spacesEtaleSite X) :
    (sliceForget U a).obj (comparisonZeroObj U a V) ⟶
      (Etale.SmallToBig.spacesEtaleToBig X).obj V :=
  Over.homMk (pullback.fst V.hom (a.app (op ⦋0⦌))) (pullback.condition)

/-- The restriction of a right-Kan-extension section to the degree-zero cartesian object. -/
private def topologySquareToZeroApp
    (F : Sheaf (sliceTotalTopology J U) (Type (u + 1))) (V : (spacesEtaleSite X)ᵒᵖ) :=
  (((sliceForget U a).op.ran.obj F.obj).map (comparisonZeroProjection U a V.unop).op) ≫
    (((sliceForget U a).op.ranAdjunction (Type (u + 1))).counit.app F.obj).app
      (op (comparisonZeroObj U a V.unop))

/-- A map to an étale target determines a canonical arrow to its degree-zero cartesian object. -/
private def comparisonReconstructionArrow (V : spacesEtaleSite X) (Y : sliceTotalSite U)
    (q : (sliceForget U a).obj Y ⟶ (Etale.SmallToBig.spacesEtaleToBig X).obj V) :
    Y ⟶ comparisonZeroObj U a V where
  base := (SimplexCategory.const ⦋0⦌ Y.base.unop 0).op
  fiber := Over.homMk
    (pullback.lift q.left
      (Y.fiber.hom ≫ U.map (SimplexCategory.const ⦋0⦌ Y.base.unop 0).op)
      (by
        exact q.w.trans ((Category.assoc _ _ _).trans
          (congrArg (fun f ↦ Y.fiber.hom ≫ f)
            ((a.naturality (SimplexCategory.const ⦋0⦌ Y.base.unop 0).op).trans
              (Category.comp_id _)))).symm))
    (pullback.lift_snd _ _ _)

/-- The degree-zero projection of an étale-augmentation direct-image section. -/
private def topologySquareSectionZero
    (F : Sheaf (sliceTotalTopology J U) (Type (u + 1))) (V : (spacesEtaleSite X)ᵒᵖ) :=
  (equalizer.ι
    (spacesEtaleAugmentationParallel U a ((topologyEtaleComparison J hJ U).pushforward.obj F) 0)
    (spacesEtaleAugmentationParallel U a ((topologyEtaleComparison J hJ U).pushforward.obj F) 1)).hom.app V

/-- Reconstruct the restriction to any total slice object using a degree-zero section. -/
private def topologySquareReconstructionApp
    (F : Sheaf (sliceTotalTopology J U) (Type (u + 1)))
    (V : (spacesEtaleSite X)ᵒᵖ)
    (x : ((topologySquareEtaleRight J hJ U a).obj F).obj.obj V)
    (Y : (sliceTotalSite U)ᵒᵖ) :
    ((sliceForget U a).op ⋙ yoneda.obj ((Etale.SmallToBig.spacesEtaleToBig X).obj V.unop)).obj Y ⟶
      F.obj.obj Y :=
  ↾fun q ↦ F.obj.map (comparisonReconstructionArrow U a V.unop Y.unop q).op
    (topologySquareSectionZero J hJ U a F V x)

/-- Canonical pullback projections and reconstructed stage sections respect restrictions and cofaces. -/
private theorem topologyEtaleCommSq_stage_compatibility :
    (∀ (F : Sheaf (sliceTotalTopology J U) (Type (u + 1)))
      {V W : (spacesEtaleSite X)ᵒᵖ} (f : V ⟶ W),
      (((topologySquareSliceRight J hJ U a).obj F).obj.map f ≫ topologySquareToZeroApp J U a F W =
        topologySquareToZeroApp J U a F V ≫
        ((spacesEtaleMorphismOfTopoi (a.app (op ⦋0⦌))).pushforward.obj
          ((spacesEtaleRestrict U ⦋0⦌).obj ((topologyEtaleComparison J hJ U).pushforward.obj F))).obj.map f)) ∧
    (∀ (F : Sheaf (sliceTotalTopology J U) (Type (u + 1)))
      (V : (spacesEtaleSite X)ᵒᵖ)
      (x : ((topologySquareEtaleRight J hJ U a).obj F).obj.obj V)
      {Y Z : (sliceTotalSite U)ᵒᵖ} (f : Y ⟶ Z),
      ((sliceForget U a).op ⋙ yoneda.obj ((Etale.SmallToBig.spacesEtaleToBig X).obj V.unop)).map f ≫
        topologySquareReconstructionApp J hJ U a F V x Z =
        topologySquareReconstructionApp J hJ U a F V x Y ≫ F.obj.map f) ∧
    (∀ (F : Sheaf (sliceTotalTopology J U) (Type (u + 1))) (V : (spacesEtaleSite X)ᵒᵖ),
      topologySquareToZeroApp J U a F V ≫
        (spacesEtaleAugmentationParallel U a ((topologyEtaleComparison J hJ U).pushforward.obj F) 0).hom.app V =
      topologySquareToZeroApp J U a F V ≫
        (spacesEtaleAugmentationParallel U a ((topologyEtaleComparison J hJ U).pushforward.obj F) 1).hom.app V) :=
  sorry

/-- The direct-image comparison from slice augmentation to étale augmentation. -/
private def topologySquareBackwardApp
    (F : Sheaf (sliceTotalTopology J U) (Type (u + 1))) :
    (topologySquareSliceRight J hJ U a).obj F ⟶ (topologySquareEtaleRight J hJ U a).obj F :=
  equalizer.lift
    (ObjectProperty.homMk
      { app := topologySquareToZeroApp J U a F
        naturality := fun _ _ f ↦ (topologyEtaleCommSq_stage_compatibility J hJ U a).1 F f })
    (by
      ext V x
      exact congrArg (fun f ↦ f x) ((topologyEtaleCommSq_stage_compatibility J hJ U a).2.2 F V))

/-- The direct-image comparison reconstructed from all stage restrictions. -/
private def topologySquareForwardSection
    (F : Sheaf (sliceTotalTopology J U) (Type (u + 1))) (V : (spacesEtaleSite X)ᵒᵖ) :
    ((topologySquareEtaleRight J hJ U a).obj F).obj.obj V ⟶
      ((topologySquareSliceRight J hJ U a).obj F).obj.obj V :=
  ↾fun x ↦ @yonedaEquiv (Over X) _
    ((Etale.SmallToBig.spacesEtaleToBig X).obj V.unop)
    ((sliceForget U a).op.ran.obj F.obj)
    (((sliceForget U a).op.ranAdjunction (Type (u + 1))).homEquiv _ _
      { app := topologySquareReconstructionApp J hJ U a F V x
        naturality := fun _ _ f ↦ (topologyEtaleCommSq_stage_compatibility J hJ U a).2.1 F V x f })

/-- The section comparisons are natural in the étale object and in the total sheaf. -/
private theorem topologyEtaleCommSq_naturality :
    (∀ (F : Sheaf (sliceTotalTopology J U) (Type (u + 1)))
      {V W : (spacesEtaleSite X)ᵒᵖ} (f : V ⟶ W),
      ((topologySquareEtaleRight J hJ U a).obj F).obj.map f ≫
        (topologySquareForwardSection J hJ U a F W) =
      (topologySquareForwardSection J hJ U a F V) ≫
        ((topologySquareSliceRight J hJ U a).obj F).obj.map f) ∧
    (∀ {F G : Sheaf (sliceTotalTopology J U) (Type (u + 1))} (α : F ⟶ G)
      (V : (spacesEtaleSite X)ᵒᵖ),
      (((topologySquareEtaleRight J hJ U a).map α).hom.app V ≫
        topologySquareForwardSection J hJ U a G V =
      topologySquareForwardSection J hJ U a F V ≫
        ((topologySquareSliceRight J hJ U a).map α).hom.app V)) :=
  sorry

/-- The forward direct-image comparison is induced by the canonical reconstruction of sections. -/
private def topologySquareForwardApp
    (F : Sheaf (sliceTotalTopology J U) (Type (u + 1))) :
    (topologySquareEtaleRight J hJ U a).obj F ⟶ (topologySquareSliceRight J hJ U a).obj F :=
  ObjectProperty.homMk
    { app := topologySquareForwardSection J hJ U a F
      naturality := fun _ _ f ↦ (topologyEtaleCommSq_naturality J hJ U a).1 F f }

/-- Restricting and reconstructing sections give mutually inverse direct-image comparisons. -/
private theorem topologyEtaleCommSq_inverse_laws
    (F : Sheaf (sliceTotalTopology J U) (Type (u + 1))) :
    topologySquareForwardApp J hJ U a F ≫ topologySquareBackwardApp J hJ U a F = 𝟙 _ ∧
    topologySquareBackwardApp J hJ U a F ≫ topologySquareForwardApp J hJ U a F = 𝟙 _ :=
  sorry

/-- Canonical direct-image compatibility of the two total augmentations. -/
private def topologyEtaleDirectImageSquare :
    topologySquareEtaleRight J hJ U a ≅ topologySquareSliceRight J hJ U a :=
  NatIso.ofComponents (fun F ↦
    { hom := topologySquareForwardApp J hJ U a F
      inv := topologySquareBackwardApp J hJ U a F
      hom_inv_id := (topologyEtaleCommSq_inverse_laws J hJ U a F).1
      inv_hom_id := (topologyEtaleCommSq_inverse_laws J hJ U a F).2 })
    (by
      intro F G α
      ext V x
      exact congrArg (fun f ↦ f x) ((topologyEtaleCommSq_naturality J hJ U a).2 α V))

/-- Canonical comparison of total inverse images for a topology finer than the étale topology. -/
def topologyEtaleCommSq :
    (spacesEtaleAugmentation U a)⁻¹ ⋙ (topologyEtaleComparison J hJ U)⁻¹ ≅
      (spacesTopologyComparison J hJ X)⁻¹ ⋙ (sliceAugmentationTopos J U a)⁻¹ :=
  Adjunction.leftAdjointCompIso (spacesEtaleAugmentation U a).adjunction
    (topologyEtaleComparison J hJ U).adjunction
    ((spacesTopologyComparison J hJ X).adjunction.comp (sliceAugmentationTopos J U a).adjunction)
    (topologyEtaleDirectImageSquare J hJ U a)

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
