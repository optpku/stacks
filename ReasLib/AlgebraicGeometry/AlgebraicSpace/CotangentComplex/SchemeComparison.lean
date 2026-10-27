/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex.UniverseLift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CotangentComplex.SiteTransport
public import ReasLib.AlgebraicGeometry.Scheme.Module.CotangentComplex
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.RestrictToScheme.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.SiteComparison
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.CotangentInverseImage
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex.Functoriality
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfSite
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.ModuleAdjunction

/-! # Scheme comparison for algebraic-space cotangent complexes -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open HomologicalComplex ComplexShape TopologicalSpace
open SheafOfModules.RingedSite

set_option backward.privateInPublic true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Cotangent

variable {S : Scheme.{u}}

/-- The scheme cotangent cochain complex pulled to the étale site and lifted in coefficients. -/
def epsilonStarSchemeCotangentCochain {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    CochainComplex (CommModules (ofOver X0)) ℤ :=
  ((DerivedQCoh.modulesLift (ofOver X0)).mapHomologicalComplex (up ℤ)).obj
    (((DerivedQCoh.SchemeRestriction.epsilonStar X0).mapHomologicalComplex (up ℤ)).obj
      (Scheme.Hom.cotangentComplex f0.left))

/-- Pullback of the scheme cotangent cochain complex is computed by the genuine module inverse image. -/
theorem epsilonStarSchemeCotangentCochain_eq {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    epsilonStarSchemeCotangentCochain f0 =
      ((DerivedQCoh.modulesLift (ofOver X0)).mapHomologicalComplex (up ℤ)).obj
        (((DerivedQCoh.SchemeRestriction.epsilonStar X0).mapHomologicalComplex (up ℤ)).obj
          (Scheme.Hom.cotangentComplex f0.left)) := rfl

/-- The pulled-back scheme cotangent complex as an object of the derived category. -/
def epsilonStarSchemeCotangent {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    DerivedCategory (CommModules (ofOver X0)) :=
  DerivedCategory.Q.obj (epsilonStarSchemeCotangentCochain f0)

/-- The derived pulled-back scheme complex is the localization of its actual cochain model. -/
theorem epsilonStarSchemeCotangent_eq {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    epsilonStarSchemeCotangent f0 =
      DerivedCategory.Q.obj (epsilonStarSchemeCotangentCochain f0) := rfl

/-- The functor of enlarged sites underlying étale-to-open restriction. -/
private def largeEpsilonBase (X0 : Over S) :
    AsSmall.{u + 1} (Opens X0.left) ⥤ AsSmall.{u + 1} (smallEtaleSite (ofOver X0)) :=
  AsSmall.down.{u, u, u + 1} ⋙ (DerivedQCoh.SchemeRestriction.epsilon X0).base ⋙
    (AsSmall.equiv.{u, u + 1, u + 1}).functor

/-- The open structure sheaf lifted to its homogeneous enlarged site. -/
private abbrev largeOpensRing (X0 : Over S) :=
  (SheafOfModules.RingedSite.CotangentComplex.UniverseLift.ringLift
    (Opens.grothendieckTopology X0.left)).obj X0.left.sheaf

/-- The lifted étale structure sheaf reindexed without a second coefficient lift. -/
private abbrev largeEtaleRing (X0 : Over S) :=
  (SiteTransport.ringReindex (ofOver X0)).obj (commStructureSheafLift (ofOver X0))

/-- Restriction of regular functions from an open to its represented étale chart. -/
private def nativeEpsilonStructureApp (X0 : Over S) (V : (Opens X0.left)ᵒᵖ) :
    X0.left.sheaf.obj.obj V ⟶
      (commStructureSheaf (ofOver X0)).obj.obj
        ((DerivedQCoh.SchemeRestriction.epsilon X0).base.op.obj V) :=
  CommRingCat.ofHom
    (((DerivedQCoh.SchemeRestriction.opensCoefficientIso X0).hom.hom.app V) ≫
      (DerivedQCoh.SchemeRestriction.epsilon X0).structureSheafMap.hom.app V).hom

/-- The enlarged structure map lifts the actual restriction of regular functions. -/
private def largeStructureApp (X0 : Over S) (V : (AsSmall.{u + 1} (Opens X0.left))ᵒᵖ) :
    (largeOpensRing X0).obj.obj V ⟶
      (largeEtaleRing X0).obj.obj ((largeEpsilonBase X0).op.obj V) :=
  (CommRingCat.universeLift.{u, u + 1}).map
    (nativeEpsilonStructureApp X0 ((AsSmall.down.{u, u, u + 1}).op.obj V))

/-- The enlarged étale-to-open presentation is a morphism of sites and its specified ring maps are natural. -/
private theorem largeEpsilon_laws (X0 : Over S) :
    IsMorphismOfSites
      (SheafOfModules.RingedSite.CotangentComplex.UniverseLift.siteTopology.{u, u, u}
        (Opens.grothendieckTopology X0.left))
      (SiteTransport.siteTopology (ofOver X0)) (largeEpsilonBase X0) ∧
    (∀ {V W} (f : V ⟶ W),
      (largeOpensRing X0).obj.map f ≫ largeStructureApp X0 W =
        largeStructureApp X0 V ≫ (largeEtaleRing X0).obj.map ((largeEpsilonBase X0).op.map f)) := sorry

/-- The enlarged base functor carries the canonical morphism-of-sites structure. -/
private instance largeEpsilonBase_isMorphismOfSites (X0 : Over S) :
    IsMorphismOfSites
      (SheafOfModules.RingedSite.CotangentComplex.UniverseLift.siteTopology.{u, u, u}
        (Opens.grothendieckTopology X0.left))
      (SiteTransport.siteTopology (ofOver X0)) (largeEpsilonBase X0) :=
  (largeEpsilon_laws X0).1

/-- The actual enlarged ringed-site morphism uses the lifted restriction maps. -/
private def largeEpsilonSite (X0 : Over S) :
    RingedSite.Hom
      (RingedSite.ofCommRingSheaf (SiteTransport.siteTopology (ofOver X0)) (largeEtaleRing X0))
      (RingedSite.ofCommRingSheaf
        (SheafOfModules.RingedSite.CotangentComplex.UniverseLift.siteTopology.{u, u, u}
          (Opens.grothendieckTopology X0.left)) (largeOpensRing X0)) where
  base := largeEpsilonBase X0
  isMorphismOfSites := largeEpsilonBase_isMorphismOfSites X0
  structureSheafMap := ObjectProperty.homMk
    { app := fun V ↦ (forget₂ CommRingCat RingCat).map (largeStructureApp X0 V)
      naturality := fun V W f ↦ congrArg ((forget₂ CommRingCat RingCat).map)
        ((largeEpsilon_laws X0).2 f) }

/-- The homogeneous ringed-topos presentation of étale-to-open restriction. -/
private def largeEpsilon (X0 : Over S) := (largeEpsilonSite X0).toToposHom

/-- The enlarged inverse-image structure map is the mate of the actual restriction of functions. -/
private def largeEpsilonSharp (X0 : Over S) :=
  RingedSite.ToposHom.commRingStructureMap (largeEpsilon X0)

/-- The geometric inverse-image functor on modules over the enlarged open structure sheaf. -/
private abbrev largeInverseImage (X0 : Over S) :=
  (largeEpsilon X0).toTopos.moduleInverseImage
    (ringSheaf.{u + 1, u + 1, u + 1} _ (largeOpensRing X0))

/-- Geometric inverse image is additive on the homogeneous presentation. -/
private instance largeInverseImage_additive (X0 : Over S) : (largeInverseImage X0).Additive :=
  (largeEpsilon X0).toTopos.moduleInverseImage_additive _

/-- The canonical coefficient isomorphism identifies the two inverse-image ring presentations. -/
private abbrev largeCoefficientEquivalence (X0 : Over S) :
    SheafOfModules.{u + 1}
        (ringSheaf.{u + 1, u + 1, u + 1} _
          ((largeEpsilon X0).toTopos.commRingInverseImage.obj (largeOpensRing X0))) ≌
      SheafOfModules.{u + 1}
        ((largeEpsilon X0).toTopos.ringInverseImage.obj
          (ringSheaf.{u + 1, u + 1, u + 1} _ (largeOpensRing X0))) :=
  SheafOfModules.ChangeOfRings.restrictScalarsEquivalence
    (SheafOfModules.RingedSite.CotangentComplex.InverseImage.coefficientIso
      (largeEpsilon X0).toTopos (B := largeOpensRing X0))

/-- Module inverse image on the enlarged presentation is geometric inverse image followed by scalar extension. -/
private def largePullback (X0 : Over S) :=
  largeInverseImage X0 ⋙ (largeCoefficientEquivalence X0).inverse ⋙
    SheafOfModules.ChangeOfRings.extendScalars.{u + 1} (ringSheafMap.{u + 1, u + 1, u + 1} (largeEpsilonSharp X0))

/-- The enlarged module inverse image retains its actual composite adjunction. -/
private def largeAdjunction (X0 : Over S) :=
  (((largeEpsilon X0).toTopos.moduleAdjunction (ringSheaf.{u + 1, u + 1, u + 1} _ (largeOpensRing X0))).comp
    (largeCoefficientEquivalence X0).symm.toAdjunction).comp
      (SheafOfModules.ChangeOfRings.extendRestrictAdjunction.{u + 1}
        (ringSheafMap.{u + 1, u + 1, u + 1} (largeEpsilonSharp X0)))

/-- The canonical étale chart associated to an open of a representing scheme. -/
private abbrev epsilonChart (X0 : Over S) (V : (Opens X0.left)ᵒᵖ) :=
  (DerivedQCoh.SchemeRestriction.epsilon X0).base.op.obj V

/-- The coefficient square uses the native inverse-image unit and the actual geometric pullback square. -/
private def nativeCoefficientUnitApp {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (V : (Opens Y0.left)ᵒᵖ) :
    Y0.left.sheaf.obj.obj V ⟶
      (commInverseImageStructureSheaf (ofOverMap f0)).obj.obj
        (epsilonChart X0 (op ((Opens.map f0.left.base).obj V.unop))) :=
  nativeEpsilonStructureApp Y0 V ≫
    (@CommRingCat.ofHom
      ((commStructureSheaf (ofOver Y0)).obj.obj (epsilonChart Y0 V))
      (((commRingPushforward (ofOverMap f0)).obj
        (commInverseImageStructureSheaf (ofOverMap f0))).obj.obj (epsilonChart Y0 V))
      (inferInstanceAs (CommRing ((commStructureSheaf (ofOver Y0)).obj.obj (epsilonChart Y0 V))))
      (inferInstanceAs (CommRing (((commRingPushforward (ofOverMap f0)).obj
        (commInverseImageStructureSheaf (ofOverMap f0))).obj.obj (epsilonChart Y0 V))))
      (((morphismOfTopoi (ofOverMap f0)).ringAdjunction.unit.app
        (structureSheaf (ofOver Y0))).hom.app (epsilonChart Y0 V)).hom) ≫
    commRingPushforwardEvaluation (ofOverMap f0)
      (commInverseImageStructureSheaf (ofOverMap f0))
      (DerivedQCoh.SchemeRestriction.smallPullbackSpaceIso f0
        ((DerivedQCoh.SchemeRestriction.epsilon Y0).base.obj V.unop)).hom ≫
    (commInverseImageStructureSheaf (ofOverMap f0)).obj.map
      ((DerivedQCoh.SchemeRestriction.restrictPullbackBaseIso f0).inv.app V.unop).op

/-- Naturality of the explicitly specified coefficient-unit components. -/
private abbrev NativeCoefficientNaturality {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) : Prop :=
  ∀ {V W : (Opens Y0.left)ᵒᵖ} (i : V ⟶ W),
    Y0.left.sheaf.obj.map i ≫ nativeCoefficientUnitApp f0 W =
      nativeCoefficientUnitApp f0 V ≫
        (commInverseImageStructureSheaf (ofOverMap f0)).obj.map
          ((DerivedQCoh.SchemeRestriction.epsilon X0).base.map
            ((Opens.map f0.left.base).map i.unop)).op

/-- The scheme inverse-image coefficient maps by the transpose of the geometric unit. -/
private def nativeCoefficientWithLaw {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (h : NativeCoefficientNaturality f0) :
    (TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf ⟶
      ((DerivedQCoh.SchemeRestriction.epsilon X0).sheafPushforwardContinuous
        (A := CommRingCat.{u})).obj (commInverseImageStructureSheaf (ofOverMap f0)) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    f0.left.toShHom.hom.base).homEquiv _ _).symm
      ⟨{ app := nativeCoefficientUnitApp f0
         naturality := fun _ _ i ↦ h i }⟩

/-- The enlarged scheme inverse-image coefficient ring. -/
private abbrev largeSchemeBase {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :=
  (SheafOfModules.RingedSite.CotangentComplex.UniverseLift.ringLift
    (Opens.grothendieckTopology X0.left)).obj
      ((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf)

/-- The inverse-image algebra of the scheme morphism on the homogeneous enlarged open site. -/
private abbrev largeSchemeAlgebra {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :=
  (SheafOfModules.RingedSite.CotangentComplex.UniverseLift.ringLift
    (Opens.grothendieckTopology X0.left)).map
      (RingedSpace.Hom.inverseImageStructureSheafHomComm f0.left.toShHom)

/-- The actual coefficient square as a morphism of enlarged ringed sites. -/
private def coefficientSiteWithLaw {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (h : NativeCoefficientNaturality f0) :
    RingedSite.Hom
      (RingedSite.ofCommRingSheaf (SiteTransport.siteTopology (ofOver X0))
        ((SiteTransport.ringReindex (ofOver X0)).obj (inverseImageLift (ofOverMap f0))))
      (RingedSite.ofCommRingSheaf
        (SheafOfModules.RingedSite.CotangentComplex.UniverseLift.siteTopology.{u, u, u}
          (Opens.grothendieckTopology X0.left)) (largeSchemeBase f0)) where
  base := largeEpsilonBase X0
  isMorphismOfSites := largeEpsilonBase_isMorphismOfSites X0
  structureSheafMap := ObjectProperty.homMk
    ((AsSmall.down.{u, u, u + 1}).op.whiskerLeft
      (Functor.whiskerRight (nativeCoefficientWithLaw f0 h).hom
        (CommRingCat.universeLift.{u, u + 1} ⋙ forget₂ CommRingCat RingCat)))

/-- The enlarged coefficient comparison is the inverse-image mate of the actual site square. -/
private def epsilonBaseMapWithLaw {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (h : NativeCoefficientNaturality f0) :=
  RingedSite.ToposHom.commRingStructureMap (coefficientSiteWithLaw f0 h).toToposHom

/-- The coefficient components are natural and their inverse-image mate commutes with the structure maps. -/
private theorem epsilonSquare_laws {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    NativeCoefficientNaturality f0 ∧
    (∀ h : NativeCoefficientNaturality f0,
      (largeEpsilon X0).toTopos.commRingInverseImage.map (largeSchemeAlgebra f0) ≫
          largeEpsilonSharp X0 =
        epsilonBaseMapWithLaw f0 h ≫
          (SiteTransport.ringReindex (ofOver X0)).map (structureMapLift (ofOverMap f0))) := sorry

/-- The canonical base comparison obtained from the geometric coefficient square. -/
private def epsilonBaseMap {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :=
  epsilonBaseMapWithLaw f0 (epsilonSquare_laws f0).1

/-- Coefficient lifting of modules on the open site of a representing scheme. -/
private abbrev sourceLift (X0 : Over S) :=
  SheafOfModules.RingedSite.CotangentComplex.UniverseLift.moduleLift
    (Opens.grothendieckTopology X0.left) X0.left.sheaf

/-- Actual étale inverse image followed by native coefficient lifting and site reindexing. -/
private def targetLift (X0 : Over S) :=
  DerivedQCoh.SchemeRestriction.epsilonStar X0 ⋙ DerivedQCoh.modulesLift (ofOver X0) ⋙
    (SiteTransport.moduleEquivalence (ofOver X0) (commStructureSheafLift (ofOver X0))).functor

/-- The enlarged right adjoint is scalar restriction followed by geometric module direct image. -/
private abbrev largeRight (X0 : Over S) :=
  SheafOfModules.restrictScalars.{u + 1}
      (ringSheafMap.{u + 1, u + 1, u + 1} (largeEpsilonSharp X0)) ⋙
    (largeCoefficientEquivalence X0).functor ⋙
      (largeEpsilon X0).toTopos.moduleRightOver
        (ringSheaf.{u + 1, u + 1, u + 1} _ (largeOpensRing X0))

/-- Forgetting the enlarged module right adjoint recovers the actual direct image of sheaves. -/
private def largeRightForgetIso (X0 : Over S) :
    largeRight X0 ⋙ CategoryTheory.Sheaf.InternalModule.ToInternal.underlying
        (ringSheaf.{u + 1, u + 1, u + 1} _ (largeOpensRing X0)) ≅
      CategoryTheory.Sheaf.InternalModule.ToInternal.underlying
        (ringSheaf.{u + 1, u + 1, u + 1} _ (largeEtaleRing X0)) ⋙
          (largeEpsilon X0).toTopos.pushforward :=
  Functor.isoWhiskerLeft
    (SheafOfModules.restrictScalars.{u + 1}
        (ringSheafMap.{u + 1, u + 1, u + 1} (largeEpsilonSharp X0)) ⋙
      (largeCoefficientEquivalence X0).functor)
    ((largeEpsilon X0).toTopos.moduleRightOverForgetIso
      (ringSheaf.{u + 1, u + 1, u + 1} _ (largeOpensRing X0)))

/-- The ordinary inverse-image unit, written in the canonical direct-image presentation on opens. -/
private def nativeUnitMap (X0 : Over S) (M : X0.left.toRingedSpace.Modules) :=
  (DerivedQCoh.SchemeRestriction.adjunction X0).unit.app M ≫
    (DerivedQCoh.SchemeRestriction.ordinaryIso X0).hom.app
      ((DerivedQCoh.SchemeRestriction.epsilonStar X0).obj M)

/-- The underlying native unit is an actual map to the sections on the represented open chart. -/
private def nativeUnitUnderlying (X0 : Over S) (M : X0.left.toRingedSpace.Modules) :
    M.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u} ⟶
      (DerivedQCoh.SchemeRestriction.epsilon X0).base.op ⋙
        ((DerivedQCoh.SchemeRestriction.epsilonStar X0).obj M).val.presheaf ⋙
          CategoryTheory.forget AddCommGrpCat.{u} :=
  Functor.whiskerRight
    ((PresheafOfModules.toPresheaf _).map (nativeUnitMap X0 M).val)
    (CategoryTheory.forget AddCommGrpCat.{u})

/-- Lift and reindex the specified native unit without assuming any right adjoint for coefficient lifting. -/
private def liftedNativeUnit (X0 : Over S) (M : X0.left.toRingedSpace.Modules) :
    (CategoryTheory.Sheaf.InternalModule.ToInternal.underlying
      (ringSheaf.{u + 1, u + 1, u + 1} _ (largeOpensRing X0))).obj ((sourceLift X0).obj M) ⟶
      (largeEpsilon X0).toTopos.pushforward.obj
        ((CategoryTheory.Sheaf.InternalModule.ToInternal.underlying
          (ringSheaf.{u + 1, u + 1, u + 1} _ (largeEtaleRing X0))).obj ((targetLift X0).obj M)) :=
  ObjectProperty.homMk ((AsSmall.down.{u, u, u + 1}).op.whiskerLeft
    (Functor.whiskerRight (nativeUnitUnderlying X0 M) CategoryTheory.uliftFunctor.{u + 1}))

/-- The lifted native unit is transported to the genuine enlarged module right adjoint. -/
private def pullbackLiftUnitUnderlying (X0 : Over S) (M : X0.left.toRingedSpace.Modules) :=
  liftedNativeUnit X0 M ≫ (largeRightForgetIso X0).inv.app ((targetLift X0).obj M)

/-- Additivity and scalar compatibility of the specified lifted unit. -/
private abbrev PullbackLiftUnitLaws (X0 : Over S) : Prop :=
  (∀ (M : X0.left.toRingedSpace.Modules) V (x y : ((sourceLift X0).obj M).val.obj V),
    CategoryTheory.Sheaf.InternalModule.underlyingApp _ (pullbackLiftUnitUnderlying X0 M) V (x + y) =
      CategoryTheory.Sheaf.InternalModule.underlyingApp _ (pullbackLiftUnitUnderlying X0 M) V x +
        CategoryTheory.Sheaf.InternalModule.underlyingApp _ (pullbackLiftUnitUnderlying X0 M) V y) ∧
  (∀ (M : X0.left.toRingedSpace.Modules) V
      (r : (ringSheaf.{u + 1, u + 1, u + 1} _ (largeOpensRing X0)).obj.obj V)
      (x : ((sourceLift X0).obj M).val.obj V),
    CategoryTheory.Sheaf.InternalModule.underlyingApp _ (pullbackLiftUnitUnderlying X0 M) V (r • x) =
      r • CategoryTheory.Sheaf.InternalModule.underlyingApp _ (pullbackLiftUnitUnderlying X0 M) V x)

/-- The enlarged-adjunction mate of the lifted native unit, with its linearity laws supplied separately. -/
private def pullbackLiftCompareWithLaws (X0 : Over S) (h : PullbackLiftUnitLaws X0)
    (M : X0.left.toRingedSpace.Modules) :
    (largePullback X0).obj ((sourceLift X0).obj M) ⟶ (targetLift X0).obj M :=
  ((largeAdjunction X0).homEquiv _ _).symm
    (CategoryTheory.Sheaf.InternalModule.homOfUnderlying.{u + 1, u + 1, u + 1}
      (ringSheaf.{u + 1, u + 1, u + 1} _ (largeOpensRing X0))
      (pullbackLiftUnitUnderlying X0 M) (h.1 M) (h.2 M))

/-- The lifted native unit is linear, and its enlarged-adjunction mates are natural in the module. -/
private theorem schemeCotangentComparison_naturality (X0 : Over S) :
    PullbackLiftUnitLaws X0 ∧
    (∀ (h : PullbackLiftUnitLaws X0) {M N : X0.left.toRingedSpace.Modules} (f : M ⟶ N),
      (largePullback X0).map ((sourceLift X0).map f) ≫ pullbackLiftCompareWithLaws X0 h N =
        pullbackLiftCompareWithLaws X0 h M ≫ (targetLift X0).map f) := sorry

/-- The canonical pullback-lift comparison is the mate of the actual lifted native unit. -/
private def pullbackLiftCompare (X0 : Over S) : sourceLift X0 ⋙ largePullback X0 ⟶ targetLift X0 where
  app := pullbackLiftCompareWithLaws X0 (schemeCotangentComparison_naturality X0).1
  naturality := fun _ _ f ↦ (schemeCotangentComparison_naturality X0).2
    (schemeCotangentComparison_naturality X0).1 f

/-- The canonical comparison between enlarged inverse image and lifted native inverse image is invertible. -/
private instance pullbackLiftCompare_isIso (X0 : Over S) : IsIso (pullbackLiftCompare X0) := sorry

/-- Restriction along the inverse-image coefficient isomorphism is additive. -/
private instance largeCoefficientInverse_additive (X0 : Over S) :
    (largeCoefficientEquivalence X0).inverse.Additive where
  map_add := by intros; rfl

/-- The enlarged module inverse image preserves sums of module morphisms. -/
private instance largePullback_additive (X0 : Over S) : (largePullback X0).Additive :=
  inferInstanceAs (largeInverseImage X0 ⋙ (largeCoefficientEquivalence X0).inverse ⋙
    SheafOfModules.ChangeOfRings.extendScalars.{u + 1}
      (ringSheafMap.{u + 1, u + 1, u + 1} (largeEpsilonSharp X0))).Additive

/-- Étale inverse image followed by native lifting and reindexing is additive. -/
private instance targetLift_additive (X0 : Over S) : (targetLift X0).Additive :=
  inferInstanceAs (DerivedQCoh.SchemeRestriction.epsilonStar X0 ⋙ DerivedQCoh.modulesLift (ofOver X0) ⋙
    (SiteTransport.moduleEquivalence (ofOver X0) (commStructureSheafLift (ofOver X0))).functor).Additive

/-- Successive inverse image, coefficient lifting, and site reindexing agree with their composite on cochains. -/
private def targetLiftCochainIso (X0 : Over S) :
    (DerivedQCoh.SchemeRestriction.epsilonStar X0).mapHomologicalComplex (up ℤ) ⋙
        (DerivedQCoh.modulesLift (ofOver X0)).mapHomologicalComplex (up ℤ) ⋙
          ((SiteTransport.moduleEquivalence (ofOver X0)
            (commStructureSheafLift (ofOver X0))).functor).mapHomologicalComplex (up ℤ) ≅
      (targetLift X0).mapHomologicalComplex (up ℤ) :=
  Functor.isoWhiskerLeft
      ((DerivedQCoh.SchemeRestriction.epsilonStar X0).mapHomologicalComplex (up ℤ))
      (Functor.mapHomologicalComplexCompIso
        (F := DerivedQCoh.modulesLift (ofOver X0))
        (G := (SiteTransport.moduleEquivalence (ofOver X0)
          (commStructureSheafLift (ofOver X0))).functor) (Iso.refl _) (up ℤ)) ≪≫
    Functor.mapHomologicalComplexCompIso
      (F := DerivedQCoh.SchemeRestriction.epsilonStar X0)
      (G := DerivedQCoh.modulesLift (ofOver X0) ⋙
        (SiteTransport.moduleEquivalence (ofOver X0)
          (commStructureSheafLift (ofOver X0))).functor)
      (H := targetLift X0) (Iso.refl _) (up ℤ)

/-- Successive geometric inverse image and coefficient changes agree with enlarged module pullback on cochains. -/
private def largePullbackCochainIso (X0 : Over S) :
    (largeInverseImage X0).mapHomologicalComplex (up ℤ) ⋙
        ((largeCoefficientEquivalence X0).inverse).mapHomologicalComplex (up ℤ) ⋙
          (SheafOfModules.ChangeOfRings.extendScalars.{u + 1}
            (ringSheafMap.{u + 1, u + 1, u + 1}
              (largeEpsilonSharp X0))).mapHomologicalComplex (up ℤ) ≅
      (largePullback X0).mapHomologicalComplex (up ℤ) :=
  Functor.isoWhiskerLeft ((largeInverseImage X0).mapHomologicalComplex (up ℤ))
      (Functor.mapHomologicalComplexCompIso
        (F := (largeCoefficientEquivalence X0).inverse)
        (G := SheafOfModules.ChangeOfRings.extendScalars.{u + 1}
          (ringSheafMap.{u + 1, u + 1, u + 1} (largeEpsilonSharp X0))) (Iso.refl _) (up ℤ)) ≪≫
    Functor.mapHomologicalComplexCompIso (F := largeInverseImage X0)
      (G := (largeCoefficientEquivalence X0).inverse ⋙
        SheafOfModules.ChangeOfRings.extendScalars.{u + 1}
          (ringSheafMap.{u + 1, u + 1, u + 1} (largeEpsilonSharp X0)))
      (H := largePullback X0) (Iso.refl _) (up ℤ)

/-- The enlarged scheme cotangent complex identifies with the coefficient lift of its native model. -/
private def schemeUniverseLiftIso {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    SheafOfModules.RingedSite.CotangentComplex.obj (largeSchemeBase f0)
        (Under.mk (largeSchemeAlgebra f0)) ≅
      ((sourceLift X0).mapHomologicalComplex (up ℤ)).obj
        (Scheme.Hom.cotangentComplex f0.left) :=
  SheafOfModules.RingedSite.CotangentComplex.UniverseLift.iso
    (Opens.grothendieckTopology X0.left)
    (RingedSpace.Hom.inverseImageStructureSheafHomComm f0.left.toShHom)

/-- The actual source comparison combines the inverse-image mate and coefficient-universe transport. -/
private def schemeCotangentTransport {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    ((targetLift X0).mapHomologicalComplex (up ℤ)).obj (Scheme.Hom.cotangentComplex f0.left) ≅
      ((largePullback X0).mapHomologicalComplex (up ℤ)).obj
        (SheafOfModules.RingedSite.CotangentComplex.obj (largeSchemeBase f0)
          (Under.mk (largeSchemeAlgebra f0))) :=
  (Functor.mapHomologicalComplexCompIso (asIso (pullbackLiftCompare X0)) (up ℤ)).symm.app
      (Scheme.Hom.cotangentComplex f0.left) ≪≫
    ((largePullback X0).mapHomologicalComplex (up ℤ)).mapIso
      (schemeUniverseLiftIso f0).symm

/-- The structure square as a morphism of algebras over the pulled scheme coefficient ring. -/
private def fixedBaseSquare {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    Under.mk ((largeEpsilon X0).toTopos.commRingInverseImage.map (largeSchemeAlgebra f0)) ⟶
      Under.mk (epsilonBaseMap f0 ≫
        (SiteTransport.ringReindex (ofOver X0)).map (structureMapLift (ofOverMap f0))) :=
  Under.homMk (largeEpsilonSharp X0)
    ((epsilonSquare_laws f0).2 (epsilonSquare_laws f0).1)

/-- The enlarged comparison applies inverse-image transport, the actual coefficient square, and native site transport. -/
private def reindexedSchemeCompareCochain {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    (((SiteTransport.moduleEquivalence (ofOver X0)
      (commStructureSheafLift (ofOver X0))).functor).mapHomologicalComplex (up ℤ)).obj
        (epsilonStarSchemeCotangentCochain f0) ⟶
      (((SiteTransport.moduleEquivalence (ofOver X0)
        (commStructureSheafLift (ofOver X0))).functor).mapHomologicalComplex (up ℤ)).obj
          (cotangentCochain (ofOverMap f0)) :=
  (targetLiftCochainIso X0).hom.app (Scheme.Hom.cotangentComplex f0.left) ≫
    (schemeCotangentTransport f0).hom ≫
    (largePullbackCochainIso X0).inv.app
      (SheafOfModules.RingedSite.CotangentComplex.obj (largeSchemeBase f0)
        (Under.mk (largeSchemeAlgebra f0))) ≫
    ((SheafOfModules.ChangeOfRings.extendScalars.{u + 1}
      (ringSheafMap.{u + 1, u + 1, u + 1} (largeEpsilonSharp X0))).mapHomologicalComplex
        (up ℤ)).map
      (SheafOfModules.RingedSite.CotangentComplex.InverseImage.iso
        (largeEpsilon X0).toTopos (largeSchemeAlgebra f0)).hom ≫
    SheafOfModules.RingedSite.CotangentComplex.map (fixedBaseSquare f0) ≫
    SheafOfModules.RingedSite.CotangentComplex.toRelativeMapCochain
      (epsilonBaseMap f0)
      ((SiteTransport.ringReindex (ofOver X0)).map (structureMapLift (ofOverMap f0))) ≫
    (SiteTransport.iso (ofOver X0) (structureMapLift (ofOverMap f0))).hom

/-- The cochain equivalence returns the enlarged étale presentation to the native one. -/
private def etaleCochainEquivalence (X0 : Over S) :=
  (SiteTransport.moduleEquivalence (ofOver X0)
    (commStructureSheafLift (ofOver X0))).mapHomologicalComplex (up ℤ)

/-- The canonical comparison from the genuine pulled-back scheme complex to the native algebraic-space complex. -/
def epsilonStarSchemeCompareCochain {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    epsilonStarSchemeCotangentCochain f0 ⟶ cotangentCochain (ofOverMap f0) :=
  ((etaleCochainEquivalence X0).unitIso.app (epsilonStarSchemeCotangentCochain f0)).hom ≫
    (etaleCochainEquivalence X0).inverse.map (reindexedSchemeCompareCochain f0) ≫
      ((etaleCochainEquivalence X0).unitIso.app (cotangentCochain (ofOverMap f0))).inv

/-- The canonical derived comparison is the localization of the actual cochain comparison. -/
def epsilonStarSchemeCompare {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    epsilonStarSchemeCotangent f0 ⟶ cotangent (ofOverMap f0) :=
  DerivedCategory.Q.map (epsilonStarSchemeCompareCochain f0)

/-- The derived comparison is computed by the canonical cochain comparison. -/
theorem epsilonStarSchemeCompare_eq {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    epsilonStarSchemeCompare f0 =
      DerivedCategory.Q.map (epsilonStarSchemeCompareCochain f0) := rfl

/-- The canonical comparison between scheme and algebraic-space cotangent complexes is invertible. -/
instance epsilonStarSchemeCompare_isIso {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    IsIso (epsilonStarSchemeCompare f0) := sorry

/-- The canonical identification of the pulled-back scheme cotangent complex with the algebraic-space cotangent complex. -/
def epsilonStarSchemeCompareIso {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    epsilonStarSchemeCotangent f0 ≅ cotangent (ofOverMap f0) :=
  asIso (epsilonStarSchemeCompare f0)

/-- The forward map of the scheme comparison is its specified canonical derived morphism. -/
theorem epsilonStarSchemeCompareIso_hom {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    (epsilonStarSchemeCompareIso f0).hom = epsilonStarSchemeCompare f0 := rfl

end AlgebraicGeometry.AlgebraicSpace.Cotangent
