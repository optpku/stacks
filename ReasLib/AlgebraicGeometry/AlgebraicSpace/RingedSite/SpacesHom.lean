module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import Mathlib.CategoryTheory.Sites.LocallyFullyFaithful
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Hom
public import ReasLib.CategoryTheory.Sites.Pullback.SheafCompose
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SpacesPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Spaces
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage

/-!
# Spaces-étale morphisms of ringed sites

A morphism of algebraic spaces induces a morphism of spaces-étale ringed sites
`(f_spaces,étale, f^♯)` with base functor `spacesEtalePullback f`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open RingedSite.ToposHom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The small étale inclusion is locally full on the spaces-étale topology. -/
instance smallEtaleInclusion_isLocallyFull (X : AlgebraicSpace S) :
    (smallEtaleToSpaces X).IsLocallyFull (spacesEtaleTopology X) :=
  sorry

/-- The functor-of-points projections of the categorical fibre product agree over the base. -/
private theorem spacesEtalePullbackInclusionSpaceIsoHom_w (f : X ⟶ Y)
    (U : smallEtaleSite Y) :
    (pullback.snd U.hom f : (pullback U.hom f).functorOfPoints ⟶ X.functorOfPoints) ≫
        homFunctor f =
      (pullback.fst U.hom f :
        (pullback U.hom f).functorOfPoints ⟶ (ofOver U.left).functorOfPoints) ≫
        homFunctor U.hom :=
  sorry

/-- The comparison map from the categorical fibre product `V ×_Y X` to the
functor-of-points fibre product used by `etaleBaseChange`. -/
def spacesEtalePullbackInclusionSpaceIsoHom (f : X ⟶ Y) (U : smallEtaleSite Y) :
    pullback U.hom f ⟶ etaleBaseChangeSpace f U :=
  let fstFun : (pullback U.hom f).functorOfPoints ⟶
      (ofOver U.left).functorOfPoints :=
    pullback.fst U.hom f
  let sndFun : (pullback U.hom f).functorOfPoints ⟶ X.functorOfPoints :=
    pullback.snd U.hom f
  pullback.lift sndFun fstFun (by exact spacesEtalePullbackInclusionSpaceIsoHom_w f U)

/-- The projections of the functor-of-points fibre product agree over the base. -/
private theorem spacesEtalePullbackInclusionSpaceIso_inv_w (f : X ⟶ Y)
    (U : smallEtaleSite Y) :
    etaleBaseChangeSnd f U ≫ U.hom = etaleBaseChangeHom f U ≫ f :=
  sorry

/-- The forward comparison followed by the inverse comparison is the identity. -/
private theorem spacesEtalePullbackInclusionSpaceIso_hom_inv_id (f : X ⟶ Y)
    (U : smallEtaleSite Y) :
    spacesEtalePullbackInclusionSpaceIsoHom f U ≫
        (pullback.lift (etaleBaseChangeSnd f U) (etaleBaseChangeHom f U)
          (spacesEtalePullbackInclusionSpaceIso_inv_w f U) :
          etaleBaseChangeSpace f U ⟶ pullback U.hom f) = 𝟙 _ :=
  sorry

/-- The inverse comparison followed by the forward comparison is the identity. -/
private theorem spacesEtalePullbackInclusionSpaceIso_inv_hom_id (f : X ⟶ Y)
    (U : smallEtaleSite Y) :
    (pullback.lift (etaleBaseChangeSnd f U) (etaleBaseChangeHom f U)
        (spacesEtalePullbackInclusionSpaceIso_inv_w f U) :
        etaleBaseChangeSpace f U ⟶ pullback U.hom f) ≫
      spacesEtalePullbackInclusionSpaceIsoHom f U = 𝟙 _ :=
  sorry

/-- The fibre product `V ×_Y X` computed in `AlgebraicSpace S` is isomorphic to the
functor-of-points fibre product used by `etaleBaseChange`. -/
def spacesEtalePullbackInclusionSpaceIso (f : X ⟶ Y) (U : smallEtaleSite Y) :
    pullback U.hom f ≅ etaleBaseChangeSpace f U where
  hom := spacesEtalePullbackInclusionSpaceIsoHom f U
  inv := pullback.lift (etaleBaseChangeSnd f U) (etaleBaseChangeHom f U)
    (by exact spacesEtalePullbackInclusionSpaceIso_inv_w f U)
  hom_inv_id := by exact spacesEtalePullbackInclusionSpaceIso_hom_inv_id f U
  inv_hom_id := by exact spacesEtalePullbackInclusionSpaceIso_inv_hom_id f U

/-- The composite `smallEtaleToSpaces Y ⋙ spacesEtalePullback f` is continuous. -/
instance smallEtaleInclusion_comp_spacesEtalePullback_isContinuous (f : X ⟶ Y) :
    (smallEtaleToSpaces Y ⋙ spacesEtalePullback f).IsContinuous
      (smallEtaleTopology Y) (spacesEtaleTopology X) :=
  Functor.isContinuous_comp (smallEtaleToSpaces Y) (spacesEtalePullback f)
    (smallEtaleTopology Y) (spacesEtaleTopology Y) (spacesEtaleTopology X)

/-- The fibre-product comparison commutes with the structure morphisms to the source. -/
private theorem smallEtaleInclusion_comp_spacesEtalePullback_app_w (f : X ⟶ Y)
    (U : smallEtaleSite Y) :
    (spacesEtalePullbackInclusionSpaceIso f U).hom ≫ ((etaleBaseChange f).obj U).hom =
      ((smallEtaleToSpaces Y ⋙ spacesEtalePullback f).obj U).hom :=
  sorry

/-- The fibre-product comparisons commute with morphisms of étale schemes. -/
private theorem smallEtaleInclusion_comp_spacesEtalePullback_naturality (f : X ⟶ Y)
    {U V : smallEtaleSite Y} (h : U ⟶ V) :
    (smallEtaleToSpaces Y ⋙ spacesEtalePullback f).map h ≫
        (MorphismProperty.Over.isoMk (spacesEtalePullbackInclusionSpaceIso f V)
          (smallEtaleInclusion_comp_spacesEtalePullback_app_w f V) :
          (smallEtaleToSpaces Y ⋙ spacesEtalePullback f).obj V ≅
            (etaleBaseChange f).obj V).hom =
      (MorphismProperty.Over.isoMk (spacesEtalePullbackInclusionSpaceIso f U)
          (smallEtaleInclusion_comp_spacesEtalePullback_app_w f U) :
          (smallEtaleToSpaces Y ⋙ spacesEtalePullback f).obj U ≅
            (etaleBaseChange f).obj U).hom ≫
        (etaleBaseChange f).map h :=
  sorry

/-- Pullback of a scheme étale over `Y` along `f` agrees, as an object of `X_spaces,étale`,
with `etaleBaseChange`. -/
def smallEtaleInclusion_comp_spacesEtalePullback (f : X ⟶ Y) :
    smallEtaleToSpaces Y ⋙ spacesEtalePullback f ≅ etaleBaseChange f :=
  NatIso.ofComponents
    (fun U ↦ MorphismProperty.Over.isoMk (spacesEtalePullbackInclusionSpaceIso f U)
      (by exact smallEtaleInclusion_comp_spacesEtalePullback_app_w f U))
    (fun h ↦ by exact smallEtaleInclusion_comp_spacesEtalePullback_naturality f h)

/-- On objects, `smallEtaleInclusion_comp_spacesEtalePullback` is
`spacesEtalePullbackInclusionSpaceIso`. -/
theorem smallEtaleInclusion_comp_spacesEtalePullback_app_left (f : X ⟶ Y)
    (U : smallEtaleSite Y) :
    ((smallEtaleInclusion_comp_spacesEtalePullback f).hom.app U).left =
      (spacesEtalePullbackInclusionSpaceIso f U).hom :=
  rfl

/-- Inverse image on spaces-étale sheaves transported through the small étale sites. -/
def spacesEtaleTypeInverseImage (f : X ⟶ Y) :
    Sheaf (spacesEtaleTopology Y) (Type u) ⥤ Sheaf (spacesEtaleTopology X) (Type u) :=
  EtaleTopos.restriction Y ⋙ EtaleTopos.inverseImage f ⋙ EtaleTopos.extension X

/-- The transported small étale direct image agrees with spaces-étale restriction. -/
def spacesEtaleTypePushforwardComparison (f : X ⟶ Y) :
    (EtaleTopos.restriction X ⋙ EtaleTopos.directImage f) ⋙ EtaleTopos.extension Y ≅
      (spacesEtalePullback f).sheafPushforwardContinuous (Type u)
        (spacesEtaleTopology Y) (spacesEtaleTopology X) :=
  Functor.isoWhiskerRight
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (EtaleTopos.restrictionExtensionIso X).symm _ ≪≫
      Functor.leftUnitor _ ≪≫
      (Functor.sheafPushforwardContinuousComp'
        (smallEtaleInclusion_comp_spacesEtalePullback f) (Type u)
        (smallEtaleTopology Y) (spacesEtaleTopology Y) (spacesEtaleTopology X)).symm)
    (EtaleTopos.extension Y) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (EtaleTopos.restrictionExtensionIso Y).symm ≪≫
    Functor.rightUnitor _

/-- The spaces-étale inverse image and restriction form the transported étale adjunction. -/
def spacesEtaleTypeAdjunction (f : X ⟶ Y) :
    spacesEtaleTypeInverseImage f ⊣
      (spacesEtalePullback f).sheafPushforwardContinuous (Type u)
        (spacesEtaleTopology Y) (spacesEtaleTopology X) :=
  ((EtaleTopos.siteEquivalence Y).toAdjunction.comp
    ((EtaleTopos.adjunction f).comp
      (EtaleTopos.siteEquivalence X).symm.toAdjunction)).ofNatIsoRight
    (spacesEtaleTypePushforwardComparison f)

/-- Continuous spaces-étale restriction is a right adjoint. -/
instance spacesEtalePullback_sheafPushforwardContinuous_type_isRightAdjoint (f : X ⟶ Y) :
    ((spacesEtalePullback f).sheafPushforwardContinuous (Type u)
      (spacesEtaleTopology Y) (spacesEtaleTopology X)).IsRightAdjoint :=
  (spacesEtaleTypeAdjunction f).isRightAdjoint

/-- The transported spaces-étale inverse image preserves finite limits. -/
instance spacesEtaleTypeInverseImage_preservesFiniteLimits (f : X ⟶ Y) :
    PreservesFiniteLimits (spacesEtaleTypeInverseImage f) := by
  change PreservesFiniteLimits
    ((EtaleTopos.siteEquivalence Y).functor ⋙ EtaleTopos.inverseImage f ⋙
      (EtaleTopos.siteEquivalence X).inverse)
  infer_instance

/-- The small-étale structure map of `f`, transported along
`smallEtaleToSpaces Y ⋙ spacesEtalePullback f ≅ etaleBaseChange f` to a map
`𝒪_Y^{small} ⟶ i_Y^* (f_spaces,étale)_* 𝒪_X`. -/
def spacesStructureSheafMapSmall (f : X ⟶ Y) :
    structureSheaf Y ⟶
      ((smallEtaleToSpaces Y).sheafPushforwardContinuous RingCat.{u}
        (smallEtaleTopology Y) (spacesEtaleTopology Y)).obj
        (((spacesEtalePullback f).sheafPushforwardContinuous RingCat.{u}
            (spacesEtaleTopology Y) (spacesEtaleTopology X)).obj
          (spacesStructureSheaf X)) :=
  EtaleRingedTopos.ringExtensionStructureMap f ≫
    (Functor.sheafPushforwardContinuousComp'
        (smallEtaleInclusion_comp_spacesEtalePullback f) RingCat.{u}
        (smallEtaleTopology Y) (spacesEtaleTopology Y) (spacesEtaleTopology X)).inv.app
      (spacesStructureSheaf X)

/-- The direct-image structure-sheaf map `𝒪_Y ⟶ (f_spaces,étale)_* 𝒪_X` on spaces-étale
sites, obtained as the cover-dense extension of the small-étale map `f^♯` along
`smallEtaleInclusion`. -/
def spacesStructureSheafMap (f : X ⟶ Y) :
    spacesStructureSheaf Y ⟶
      ((spacesEtalePullback f).sheafPushforwardContinuous RingCat.{u}
        (spacesEtaleTopology Y) (spacesEtaleTopology X)).obj
        (spacesStructureSheaf X) :=
  InducedCategory.homMk
    (Functor.IsCoverDense.sheafHom
      (((EtaleRingedTopos.ringExtensionRestrictionIso Y).hom.app (structureSheaf Y)).hom ≫
        (spacesStructureSheafMapSmall f).hom))

/-- Restriction of `spacesStructureSheafMap` along `smallEtaleToSpaces Y` recovers
`spacesStructureSheafMapSmall`. -/
theorem spacesStructureSheafMapSmall_spec (f : X ⟶ Y) :
    (EtaleRingedTopos.ringExtensionRestrictionIso Y).hom.app (structureSheaf Y) ≫
      spacesStructureSheafMapSmall f =
    ((smallEtaleToSpaces Y).sheafPushforwardContinuous RingCat.{u}
          (smallEtaleTopology Y) (spacesEtaleTopology Y)).map
        (spacesStructureSheafMap f) :=
  sorry

/-- The morphism of spaces-étale ringed sites associated to a morphism of algebraic spaces. -/
def spacesRingedHom (f : X ⟶ Y) :
    RingedSite.Hom (spacesRingedSite X) (spacesRingedSite Y) where
  base := spacesEtalePullback f
  isMorphismOfSites := spacesEtalePullback_isMorphismOfSites f
  structureSheafMap := spacesStructureSheafMap f

/-- The base functor of `spacesRingedHom f` is `spacesEtalePullback f`. -/
@[simp]
theorem spacesRingedHom_base (f : X ⟶ Y) :
    (spacesRingedHom f).base = spacesEtalePullback f :=
  rfl

/-- The structure-sheaf map of `spacesRingedHom f` is `spacesStructureSheafMap f`. -/
@[simp]
theorem spacesRingedHom_structureSheafMap (f : X ⟶ Y) :
    (spacesRingedHom f).structureSheafMap = spacesStructureSheafMap f :=
  rfl

/-- Coefficient-forgetful comparison for continuous pushforward along `spacesEtalePullback`. -/
def spacesRingedHom_forgetIso (f : X ⟶ Y) :
    (spacesEtalePullback f).sheafPushforwardContinuous RingCat.{u}
          (spacesEtaleTopology Y) (spacesEtaleTopology X) ⋙
        sheafCompose (spacesEtaleTopology Y) (forget RingCat.{u}) ≅
      sheafCompose (spacesEtaleTopology X) (forget RingCat.{u}) ⋙
        (spacesEtalePullback f).sheafPushforwardContinuous (Type u)
          (spacesEtaleTopology Y) (spacesEtaleTopology X) :=
  eqToIso
    (Functor.sheafPushforwardContinuous.compSheafCompose (spacesEtalePullback f)
      (forget RingCat.{u}) (spacesEtaleTopology Y) (spacesEtaleTopology X))

/-- The type-valued morphism of topoi presented by `spacesEtalePullback f` on sheaves of
types in universe `u`. -/
def spacesRingedMorphismOfTopoi (f : X ⟶ Y) :
    MorphismOfTopoiIn.{u + 1, u + 1, u + 1, u + 1, u}
      (spacesEtaleTopology Y) (spacesEtaleTopology X) where
  inverseImageFunctor :=
    LeftExactFunctor.of (spacesEtaleTypeInverseImage f)
  pushforward :=
    (spacesEtalePullback f).sheafPushforwardContinuous (Type u)
      (spacesEtaleTopology Y) (spacesEtaleTopology X)
  adjunction :=
    spacesEtaleTypeAdjunction f

/-- The direct image of `spacesRingedMorphismOfTopoi f` is continuous sheaf pushforward
along `spacesEtalePullback f`. -/
theorem spacesRingedMorphismOfTopoi_pushforward (f : X ⟶ Y) :
    (spacesRingedMorphismOfTopoi f).pushforward =
      (spacesEtalePullback f).sheafPushforwardContinuous (Type u)
        (spacesEtaleTopology Y) (spacesEtaleTopology X) :=
  rfl

/-- Direct-image ring compatibility of `spacesRingedHom f`. -/
theorem spacesRingedHom_isRingCompatible (f : X ⟶ Y) :
    @Direct.IsRingCompatible (spacesRingedSite X) (spacesRingedSite Y) _ _
      (spacesRingedMorphismOfTopoi f)
      ((spacesEtalePullback f).sheafPushforwardContinuous RingCat.{u}
        (spacesEtaleTopology Y) (spacesEtaleTopology X))
      (spacesRingedHom_forgetIso f) (spacesStructureSheafMap f) :=
  sorry

/-- The morphism of spaces-étale ringed topoi associated to a morphism of algebraic spaces,
packaged by `ofDirectImage` so that `UnivLE.{u+1,u}` is not required. -/
def spacesRingedToposHom (f : X ⟶ Y) :
    RingedSite.ToposHom (spacesRingedSite X) (spacesRingedSite Y) :=
  @ofDirectImage (spacesRingedSite X) (spacesRingedSite Y) _ _
    (spacesRingedMorphismOfTopoi f)
    ((spacesEtalePullback f).sheafPushforwardContinuous RingCat.{u}
      (spacesEtaleTopology Y) (spacesEtaleTopology X))
    (spacesRingedHom_forgetIso f) (spacesStructureSheafMap f)
    (spacesRingedHom_isRingCompatible f)

/-- `spacesRingedToposHom f` is the `ofDirectImage` packaging of `spacesRingedHom f`. -/
theorem spacesRingedToposHom_eq (f : X ⟶ Y) :
    spacesRingedToposHom f =
      @ofDirectImage (spacesRingedSite X) (spacesRingedSite Y) _ _
        (spacesRingedMorphismOfTopoi f)
        ((spacesEtalePullback f).sheafPushforwardContinuous RingCat.{u}
          (spacesEtaleTopology Y) (spacesEtaleTopology X))
        (spacesRingedHom_forgetIso f) (spacesStructureSheafMap f)
        (spacesRingedHom_isRingCompatible f) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
