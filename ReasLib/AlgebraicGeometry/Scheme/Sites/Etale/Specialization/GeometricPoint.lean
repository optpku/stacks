/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.StrictHenselianSections

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

@[expose] public section

set_option backward.privateInPublic true

noncomputable section

namespace AlgebraicGeometry.Scheme

variable [∀ X : Scheme.{u}, HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]

/-- Construct the Kan extensions used by inverse image explicitly. -/
private abbrev geometricPullbackExtensionExists {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : Y.Etaleᵒᵖ ⥤ Type (u + 1)) :
    (smallEtalePullback f).op.HasLeftKanExtension P :=
  (@Functor.pointwiseLeftKanExtensionIsUniversal _ _ _ _ _ _
    (smallEtalePullback f).op P (fun U ↦ @HasColimitsOfShape.has_colimit _ _ _ _
      (HasColimitsOfSize.has_colimits_of_shape (C := Type (u + 1))
        (CostructuredArrow (smallEtalePullback f).op U)) _)).hasInitial

/-- Germs of twice-pulled-back sections along a geometric lift into a pointed strict
henselization, transported through both inverse-image stalk comparisons. -/
def geometricPullbackSectionsToStalk {S : Scheme.{u}} (s t : GeometricPoint S)
    (point : Spec (.of t.K) ⟶ strictHenselizationAt S s)
    (point_over : point ≫ StrictHenselization.toScheme S s = t.hom)
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) :
    @etalePullbackIdentitySections _ _ point inferInstance
        (geometricPullbackExtensionExists point)
        ((@Sheaf.smallEtaleInverseImage _ _ (StrictHenselization.toScheme S s)
          (Type (u + 1)) inferInstance inferInstance
          (geometricPullbackExtensionExists (StrictHenselization.toScheme S s))).obj F) → t.toSmallEtalePoint.sheafFiber.obj F :=
  let structural := StrictHenselization.toScheme S s
  let geometric := @GeometricPoint.of (Spec (.of t.K)) t.K inferInstance
    t.isAlgClosed (𝟙 _)
  let lifted := @GeometricPoint.of (strictHenselizationAt S s) t.K inferInstance
    t.isAlgClosed point
  let identityObject : (strictHenselizationAt S s).Etale :=
    MorphismProperty.Over.mk _ (𝟙 _) inferInstance
  let pulledIdentity := (smallEtalePullback point).obj identityObject
  let pulled := (@Sheaf.smallEtaleInverseImage _ _ structural (Type (u + 1))
    inferInstance inferInstance (geometricPullbackExtensionExists structural)).obj F
  let twicePulled := (@Sheaf.smallEtaleInverseImage _ _ point (Type (u + 1))
    inferInstance inferInstance (geometricPullbackExtensionExists point)).obj pulled
  let pointLift := pullback.lift point (𝟙 (Spec (.of t.K)))
    ((Category.comp_id point).trans (Category.id_comp point).symm)
  let liftOver : Over.mk geometric.hom ⟶ (Etale.forget _).obj pulledIdentity :=
    Over.homMk pointLift
      (pullback.lift_snd point (𝟙 (Spec (.of t.K)))
        ((Category.comp_id point).trans (Category.id_comp point).symm))
  let liftedOverIso : Over.mk (geometric.hom ≫ point) ≅ Over.mk lifted.hom :=
    Over.isoMk (Iso.refl _) (Category.id_comp point).symm
  let liftedTransport := Functor.whiskerLeft (Etale.forget (strictHenselizationAt S s))
    (coyoneda.map liftedOverIso.inv.op)
  let targetOverIso : Over.mk (lifted.hom ≫ structural) ≅ Over.mk t.hom :=
    Over.isoMk (Iso.refl _) ((Category.id_comp t.hom).trans point_over.symm)
  let targetTransport := Functor.whiskerLeft (Etale.forget S)
    (coyoneda.map targetOverIso.inv.op)
  geometric.toSmallEtalePoint.toPresheafFiber pulledIdentity liftOver twicePulled.obj ≫
    (geometric.toSmallEtalePoint.sheafFiberComapIsoOfMorphismOfSites
      (J := (strictHenselizationAt S s).smallEtaleTopology)
      (h_adj := (@Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        _ _ _ _ (smallEtalePullback point) (Type (u + 1)) inferInstance
        (strictHenselizationAt S s).smallEtaleTopology _ inferInstance
        (geometricPullbackExtensionExists point) inferInstance).isRightAdjoint)
      (h_small := smallEtalePullback_fiber_initiallySmall point t.K geometric.hom)
      (smallEtalePullback point) (Type (u + 1))).inv.app pulled ≫
    (GrothendieckTopology.Point.Hom.sheafFiber
      ⟨smallEtaleInverseImage_comapFiberHom point geometric⟩).app pulled ≫
    (GrothendieckTopology.Point.Hom.sheafFiber ⟨liftedTransport⟩).app pulled ≫
    (lifted.toSmallEtalePoint.sheafFiberComapIsoOfMorphismOfSites
      (J := S.smallEtaleTopology)
      (h_adj := (@Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        _ _ _ _ (smallEtalePullback structural) (Type (u + 1)) inferInstance
        S.smallEtaleTopology _ inferInstance
        (geometricPullbackExtensionExists structural) inferInstance).isRightAdjoint)
      (h_small := smallEtalePullback_fiber_initiallySmall structural t.K lifted.hom)
      (smallEtalePullback structural) (Type (u + 1))).inv.app F ≫
    (GrothendieckTopology.Point.Hom.sheafFiber
      ⟨smallEtaleInverseImage_comapFiberHom structural lifted⟩).app F ≫
    (GrothendieckTopology.Point.Hom.sheafFiber ⟨targetTransport⟩).app F

/-- Geometric-point sections of the twice-pulled-back sheaf are identified with
the original geometric stalk by the canonical germ map. -/
theorem geometricPullbackSectionsToStalk_bijective {S : Scheme.{u}}
    (s t : GeometricPoint S) (point : Spec (.of t.K) ⟶ strictHenselizationAt S s)
    (point_over : point ≫ StrictHenselization.toScheme S s = t.hom)
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) :
    Function.Bijective (geometricPullbackSectionsToStalk s t point point_over F) := sorry

/-- Specialization of geometric stalks agrees with sections pullback from the
pointed strict henselization along the chosen geometric lift. -/
theorem etaleSpecialization_eq_geometricPullback {S : Scheme.{u}}
    (s t : GeometricPoint S) (point : Spec (.of t.K) ⟶ strictHenselizationAt S s)
    (point_over : point ≫ StrictHenselization.toScheme S s = t.hom)
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) :
    (strictHenselianGlobalToStalk (Type (u + 1)) s).app F ≫
        ((StrictHenselianNeighborhood.canonical s).specializationPoint
          point point_over).sheafFiber.app F =
      TypeCat.ofHom (@etaleSectionsPullback _ _ point inferInstance inferInstance
        (geometricPullbackExtensionExists point)
        ((@Sheaf.smallEtaleInverseImage _ _ (StrictHenselization.toScheme S s)
          (Type (u + 1)) inferInstance inferInstance
          (geometricPullbackExtensionExists (StrictHenselization.toScheme S s))).obj F)) ≫
        TypeCat.ofHom (geometricPullbackSectionsToStalk s t point point_over F) := sorry

end AlgebraicGeometry.Scheme

end
