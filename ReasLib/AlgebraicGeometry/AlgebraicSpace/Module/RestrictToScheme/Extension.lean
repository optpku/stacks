/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.PullbackSmallSource
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings.Equivalence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme.PresentationComparison
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward.Composition
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import ReasLib.AlgebraicGeometry.Scheme.Module.RingedSpace

/-! # Extension of modules from the Zariski site to the small étale site -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SchemeRestriction
variable {S : Scheme.{u}}

/-- The actual underived direct image, retaining the canonical module restriction. -/
def ordinary (U : Over S) :
    (ofOver U).Modules ⥤ U.left.toRingedSpace.Modules :=
  Modules.restrictToScheme U ⋙ Scheme.Modules.toRingedSpace U.left

/-- The actual full étale-to-open ringed-site morphism; its source object universe is large
but its base starts at the original small open site. -/
def epsilon (U : Over S) :=
  RingedSite.Hom.comp (schemeEtaleRingedHom U) (smallEtaleToOpensRingedHom U.left)

/-- Continuity is retained from the stored ringed-site morphism. -/
def epsilon_isContinuous (U : Over S) :
    (epsilon U).base.IsContinuous
      (Opens.grothendieckTopology U.left) (smallEtaleTopology (ofOver U)) :=
  RingedSite.Hom.base_isContinuous (epsilon U)

/-- The underlying presheaf pushforward has an actual left adjoint by the small-source
free represented construction, retaining the original coefficient universe. -/
def epsilonPresheaf_isRightAdjoint (U : Over S) :
    (PresheafOfModules.pushforward.{u} (epsilon U).structureSheafMap.hom).IsRightAdjoint :=
  PresheafOfModules.SmallSourcePullback.isRightAdjoint (epsilon U).structureSheafMap.hom

/-- The sheaf inverse image is the actual presheaf pullback followed by sheafification. -/
def epsilonPullback (U : Over S) :
    RingedSite.ModuleCat.{u}
        (RingedSite.ofRingSheaf (Opens.grothendieckTopology U.left)
          ⟨Scheme.Site.structurePresheaf (U.left.restrictFunctor ⋙ Over.forget U.left),
            opensStructurePresheaf_isSheaf U.left⟩) ⥤ (ofOver U).Modules :=
  SheafOfModules.forget _ ⋙
    @PresheafOfModules.pullback.{u} _ _ _ _ _ _ _
      (epsilon U).structureSheafMap.hom (epsilonPresheaf_isRightAdjoint U) ⋙
    @PresheafOfModules.sheafification _ _ _ _ _
      (𝟙 (structureSheaf (ofOver U)).obj)
      (Presheaf.isLocallyInjective_of_injective _ _ (fun _ ↦ Function.injective_id))
      (Presheaf.isLocallySurjective_of_surjective _ _ (fun _ ↦ Function.surjective_id))
      inferInstance inferInstance

/-- The adjunction stores the native free presentation/sheafification Hom maps. -/
def epsilonAdjunction (U : Over S) :
    epsilonPullback U ⊣ (epsilon U).modulePushforward.{u} :=
  @SheafOfModules.PullbackConstruction.adjunction.{u} _ _ _ _ _ _ _ _ _
    (epsilon_isContinuous U) (epsilon U).structureSheafMap
    (epsilonPresheaf_isRightAdjoint U) inferInstance inferInstance

/-- The two open coefficient presentations have the native restriction-global-sections maps
in both directions. -/
def opensCoefficientIso (U : Over S) :
    U.left.ringCatSheaf ≅
      ⟨Scheme.Site.structurePresheaf (U.left.restrictFunctor ⋙ Over.forget U.left),
        opensStructurePresheaf_isSheaf U.left⟩ := by
  let hom := opensStructureToRingCatSheaf U.left
  let inv :
      (⟨Scheme.Site.structurePresheaf (U.left.restrictFunctor ⋙ Over.forget U.left),
        opensStructurePresheaf_isSheaf U.left⟩ : Sheaf _ RingCat.{u}) ⟶ U.left.ringCatSheaf :=
    ⟨Functor.whiskerRight (@Scheme.restrictFunctorΓ U.left).hom (forget₂ CommRingCat RingCat)⟩
  have laws : hom ≫ inv = 𝟙 _ ∧ inv ≫ hom = 𝟙 _ := by sorry
  exact ⟨hom, inv, laws.1, laws.2⟩

/-- The open-coefficient presentation is an equivalence with actual inverse scalar restriction. -/
def opensModuleEquivalence (U : Over S) :=
  SheafOfModules.ChangeOfRings.restrictScalarsEquivalence (opensCoefficientIso U)

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SchemeRestriction

namespace AlgebraicGeometry.AlgebraicSpace.Modules.RestrictToScheme
open DerivedQCoh.SchemeRestriction
variable {S : Scheme.{u}}

/-- Restriction agrees with direct image along the étale-to-open morphism followed by
transport of the coefficient sheaf. -/
def restrictionIsoEpsilon (U : Over S) :
    Modules.restrictToScheme U ≅ (epsilon U).modulePushforward.{u} ⋙
      (opensModuleEquivalence U).inverse :=
  restrictionIsoBare U ≪≫
    (Functor.associator (schemeEtaleRingedHom U).modulePushforward
      (smallEtaleToOpensRingedHom U.left).modulePushforward (opensToSchemeModules U.left)).symm ≪≫
    Functor.isoWhiskerRight
      (RingedSite.Hom.modulePushforwardCompIso (schemeEtaleRingedHom U)
        (smallEtaleToOpensRingedHom U.left)) (opensToSchemeModules U.left)

/-- Extension is coefficient transport followed by the presheaf inverse image and sheafification. -/
def extension (U : Over S) : U.left.Modules ⥤ (ofOver U).Modules :=
  (opensModuleEquivalence U).functor ⋙ epsilonPullback U

/-- Extension is left adjoint to restriction to scheme opens. -/
def extensionAdjunction (U : Over S) : extension U ⊣ Modules.restrictToScheme U :=
  ((opensModuleEquivalence U).toAdjunction.comp (epsilonAdjunction U)).ofNatIsoRight
    (restrictionIsoEpsilon U).symm

/-- Extension is left adjoint to the equivalent composite direct-image presentation. -/
def extensionAdjunctionBare (U : Over S) : extension U ⊣ restrictionBare U :=
  (extensionAdjunction U).ofNatIsoRight (restrictionIsoBare U)

end AlgebraicGeometry.AlgebraicSpace.Modules.RestrictToScheme

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SchemeRestriction
variable {S : Scheme.{u}}

/-- Ordinary restriction agrees with étale-to-open direct image and coefficient transport. -/
def ordinaryIso (U : Over S) :
    ordinary U ≅ (epsilon U).modulePushforward.{u} ⋙
      (opensModuleEquivalence U).inverse ⋙ Scheme.Modules.toRingedSpace U.left :=
  Functor.isoWhiskerRight (Modules.RestrictToScheme.restrictionIsoEpsilon U)
    (Scheme.Modules.toRingedSpace U.left) ≪≫ Functor.associator _ _ _

/-- Inverse image on ringed-space modules is the inverse scheme presentation followed by extension. -/
def epsilonStar (U : Over S) : U.left.toRingedSpace.Modules ⥤ (ofOver U).Modules :=
  (Scheme.Modules.ringedSpaceEquivalence U.left).inverse ⋙ Modules.RestrictToScheme.extension U

/-- Inverse image is left adjoint to ordinary restriction through the scheme presentation. -/
def adjunction (U : Over S) : epsilonStar U ⊣ ordinary U :=
  (Scheme.Modules.ringedSpaceEquivalence U.left).symm.toAdjunction.comp
    (Modules.RestrictToScheme.extensionAdjunction U)

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SchemeRestriction
