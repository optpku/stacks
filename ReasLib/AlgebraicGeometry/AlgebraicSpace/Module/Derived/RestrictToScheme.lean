module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.KInjectiveModel
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.PullbackSmallSource
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings.Equivalence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme.PresentationComparison
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward.Composition
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Grothendieck
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme
public import ReasLib.AlgebraicGeometry.Scheme.Module.RingedSpace
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Structure

/-! # Right-derived restriction to a represented scheme

Restriction is the direct image from the étale ringed topos to the Zariski ringed topos.
It is computed on an actual unbounded K-injective replacement in the original module universe.
The source-facing functor is restricted to complexes with quasi-coherent cohomology.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}}

/-- Restriction followed by the actual identity-on-data ringed-space presentation is additive. -/
instance instAdditive_restrictToScheme_toRingedSpace (U : Over S) :
    (Modules.restrictToScheme U ⋙ Scheme.Modules.toRingedSpace U.left).Additive := sorry

namespace SchemeRestriction

/-- The actual underived direct image, retaining the canonical module restriction. -/
def ordinary (U : Over S) :
    (ofOver U).Modules ⥤ U.left.toRingedSpace.Modules :=
  Modules.restrictToScheme U ⋙ Scheme.Modules.toRingedSpace U.left

/-- Additivity uses the same actual composite functor under its local canonical spelling. -/
instance ordinary_additive (U : Over S) : (ordinary U).Additive :=
  instAdditive_restrictToScheme_toRingedSpace U

/-- The actual full étale-to-open ringed-site morphism; its source object universe is large
but its base starts at the original small open site. -/
def epsilon (U : Over S) :=
  RingedSite.Hom.comp (schemeEtaleRingedHom U) (smallEtaleToOpensRingedHom U.left)

/-- Continuity is retained from the stored ringed-site morphism. -/
instance epsilon_isContinuous (U : Over S) :
    (epsilon U).base.IsContinuous
      (Opens.grothendieckTopology U.left) (smallEtaleTopology (ofOver U)) :=
  RingedSite.Hom.base_isContinuous (epsilon U)

/-- The underlying presheaf pushforward has an actual left adjoint by the small-source
free represented construction, retaining the original coefficient universe. -/
instance epsilonPresheaf_isRightAdjoint (U : Over S) :
    (PresheafOfModules.pushforward.{u} (epsilon U).structureSheafMap.hom).IsRightAdjoint :=
  PresheafOfModules.SmallSourcePullback.isRightAdjoint (epsilon U).structureSheafMap.hom

/-- The sheaf inverse image is the actual presheaf pullback followed by sheafification. -/
def epsilonPullback (U : Over S) :
    RingedSite.ModuleCat.{u}
        (RingedSite.ofRingSheaf (Opens.grothendieckTopology U.left)
          ⟨Scheme.Site.structurePresheaf (U.left.restrictFunctor ⋙ Over.forget U.left),
            opensStructurePresheaf_isSheaf U.left⟩) ⥤ (ofOver U).Modules := by
  letI : Presheaf.IsLocallyInjective (smallEtaleTopology (ofOver U))
      (𝟙 (structureSheaf (ofOver U)).obj) :=
    Presheaf.isLocallyInjective_of_injective _ _ (fun _ ↦ Function.injective_id)
  letI : Presheaf.IsLocallySurjective (smallEtaleTopology (ofOver U))
      (𝟙 (structureSheaf (ofOver U)).obj) :=
    Presheaf.isLocallySurjective_of_surjective _ _ (fun _ ↦ Function.surjective_id)
  exact SheafOfModules.forget _ ⋙
    PresheafOfModules.pullback.{u} (epsilon U).structureSheafMap.hom ⋙
    PresheafOfModules.sheafification (R := structureSheaf (ofOver U))
      (R₀ := (structureSheaf (ofOver U)).obj) (𝟙 (structureSheaf (ofOver U)).obj)

/-- The adjunction stores the native free presentation/sheafification Hom maps. -/
def epsilonAdjunction (U : Over S) :
    epsilonPullback U ⊣ (epsilon U).modulePushforward.{u} :=
  SheafOfModules.PullbackConstruction.adjunction (epsilon U).structureSheafMap

/-- The two open coefficient presentations have the native restriction-global-sections maps
in both directions. -/
def opensCoefficientIso (U : Over S) :
    U.left.ringCatSheaf ≅
      ⟨Scheme.Site.structurePresheaf (U.left.restrictFunctor ⋙ Over.forget U.left),
        opensStructurePresheaf_isSheaf U.left⟩ where
  hom := opensStructureToRingCatSheaf U.left
  inv := ⟨Functor.whiskerRight (@Scheme.restrictFunctorΓ U.left).hom (forget₂ CommRingCat RingCat)⟩
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The open-coefficient presentation is an equivalence with actual inverse scalar restriction. -/
def opensModuleEquivalence (U : Over S) :=
  SheafOfModules.ChangeOfRings.restrictScalarsEquivalence (opensCoefficientIso U)

/-- Ordinary restriction agrees with the actual ringed-site direct image and coefficient
presentation. Every comparison has both section maps specified by the canonical owners. -/
def ordinaryIso (U : Over S) :
    ordinary U ≅ (epsilon U).modulePushforward.{u} ⋙
      (opensModuleEquivalence U).inverse ⋙ Scheme.Modules.toRingedSpace U.left :=
  Functor.isoWhiskerRight (Modules.RestrictToScheme.restrictionIsoBare U)
      (Scheme.Modules.toRingedSpace U.left) ≪≫
    Functor.isoWhiskerRight
      ((Functor.associator (schemeEtaleRingedHom U).modulePushforward
        (smallEtaleToOpensRingedHom U.left).modulePushforward (opensToSchemeModules U.left)).symm ≪≫
        Functor.isoWhiskerRight
          (RingedSite.Hom.modulePushforwardCompIso (schemeEtaleRingedHom U)
            (smallEtaleToOpensRingedHom U.left)) (opensToSchemeModules U.left))
      (Scheme.Modules.toRingedSpace U.left) ≪≫
    Functor.associator _ _ _

/-- Exact étale inverse image, transported through the actual open and ringed-space
presentation equivalences. -/
def epsilonStar (U : Over S) : U.left.toRingedSpace.Modules ⥤ (ofOver U).Modules :=
  (Scheme.Modules.ringedSpaceEquivalence U.left).inverse ⋙
    (opensModuleEquivalence U).functor ⋙ epsilonPullback U

/-- The actual underived adjunction uses native free-presentation inverse image and the given
presentation equivalences, then the specified comparison with canonical restriction. -/
def adjunction (U : Over S) : epsilonStar U ⊣ ordinary U :=
  (((Scheme.Modules.ringedSpaceEquivalence U.left).symm.toAdjunction).comp
    (((opensModuleEquivalence U).toAdjunction).comp (epsilonAdjunction U))).ofNatIsoRight
      (ordinaryIso U).symm

/-- The inverse image is additive through its actual module adjunction. -/
instance epsilonStar_additive (U : Over S) : (epsilonStar U).Additive := sorry

/-- Étale-to-Zariski inverse image is exact. This is the source's flat topology-change morphism. -/
instance epsilonStar_preservesFiniteLimits (U : Over S) :
    PreservesFiniteLimits (epsilonStar U) := sorry

/-- The specified inverse image is a left adjoint and preserves finite colimits. -/
instance epsilonStar_preservesFiniteColimits (U : Over S) :
    PreservesFiniteColimits (epsilonStar U) := by
  letI : PreservesColimits (epsilonStar U) := (adjunction U).leftAdjoint_preservesColimits
  infer_instance

/-- Exact inverse image descends by the native exact-functor localization construction. -/
def epsilonStarDerived (U : Over S) :
    RingedSpace.ModuleDerived U.left.toRingedSpace ⥤ ModuleDerived (ofOver U) :=
  (epsilonStar U).mapDerivedCategory

/-- The actual unbounded right-derived restriction uses the shared K-injective model factory. -/
def derived (U : Over S) :
    ModuleDerived (ofOver U) ⥤ RingedSpace.ModuleDerived U.left.toRingedSpace :=
  Functor.KInjectiveModel.derived.{u} (ordinary U)

/-- The unit cochain map first uses the actual inverse-image/direct-image unit, then applies
ordinary direct image to the specified K-injective augmentation of the inverse image. -/
def unitOnCochains (U : Over S) (A : CochainComplex U.left.toRingedSpace.Modules ℤ) :
    A ⟶ ((ordinary U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((CochainComplex.KInjectiveResolution.Construction.replacement.{u} (ofOver U).Modules).obj
        (((epsilonStar U).mapHomologicalComplex (ComplexShape.up ℤ)).obj A)) :=
  (Functor.mapHomologicalComplexIdIso U.left.toRingedSpace.Modules
      (ComplexShape.up ℤ)).inv.app A ≫
    (NatTrans.mapHomologicalComplex (adjunction U).unit (ComplexShape.up ℤ)).app A ≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (epsilonStar U ⋙ ordinary U))
      (ComplexShape.up ℤ)).inv.app A ≫
    ((ordinary U).mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((CochainComplex.KInjectiveResolution.Construction.augmentation.{u}
        (ofOver U).Modules).app
          (((epsilonStar U).mapHomologicalComplex (ComplexShape.up ℤ)).obj A))

/-- The adjunction unit is a quasi-isomorphism for complexes with quasi-coherent cohomology,
as in `lemma-derived-quasi-coherent-small-etale-site`. -/
theorem unitOnCochains_quasiIso (U : Over S)
    (A : CochainComplex U.left.toRingedSpace.Modules ℤ)
    (hA : Scheme.derivedQuasiCoherentModuleProperty U.left (DerivedCategory.Q.obj A)) :
    QuasiIso (unitOnCochains U A) := sorry

/-- The counit cochain map is the actual underived counit on the specified K-injective model. -/
def counitOnCochains (U : Over S) (E : CochainComplex (ofOver U).Modules ℤ) :
    ((epsilonStar U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((ordinary U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((CochainComplex.KInjectiveResolution.Construction.replacement.{u}
          (ofOver U).Modules).obj E)) ⟶
      (CochainComplex.KInjectiveResolution.Construction.replacement.{u}
        (ofOver U).Modules).obj E :=
  (Functor.mapHomologicalComplexCompIso (Iso.refl (ordinary U ⋙ epsilonStar U))
      (ComplexShape.up ℤ)).hom.app
        ((CochainComplex.KInjectiveResolution.Construction.replacement.{u}
          (ofOver U).Modules).obj E) ≫
    (NatTrans.mapHomologicalComplex (adjunction U).counit (ComplexShape.up ℤ)).app
      ((CochainComplex.KInjectiveResolution.Construction.replacement.{u}
        (ofOver U).Modules).obj E) ≫
    (Functor.mapHomologicalComplexIdIso (ofOver U).Modules (ComplexShape.up ℤ)).hom.app
      ((CochainComplex.KInjectiveResolution.Construction.replacement.{u}
        (ofOver U).Modules).obj E)

/-- On a complex with quasi-coherent cohomology, the actual model counit induces the original
quasi-coherent sheaves on cohomology. -/
theorem counitOnCochains_quasiIso (U : Over S) (E : CochainComplex (ofOver U).Modules ℤ)
    (hE : derivedQuasiCoherentModuleProperty (ofOver U) (DerivedCategory.Q.obj E)) :
    QuasiIso (counitOnCochains U E) := sorry

/-- The unit isomorphism localizes the displayed cochain unit; its reverse is the formal
quasi-isomorphism inverse, followed by the native model and exact-functor comparisons. -/
def unitOnInput (U : Over S) (A : CochainComplex U.left.toRingedSpace.Modules ℤ)
    (hA : Scheme.derivedQuasiCoherentModuleProperty U.left (DerivedCategory.Q.obj A)) :
    DerivedCategory.Q.obj A ≅
      (epsilonStarDerived U ⋙ derived U).obj (DerivedCategory.Q.obj A) :=
  Localization.isoOfHom (DerivedCategory.Q (C := U.left.toRingedSpace.Modules))
      (HomologicalComplex.quasiIso U.left.toRingedSpace.Modules (ComplexShape.up ℤ))
      (unitOnCochains U A) (unitOnCochains_quasiIso U A hA) ≪≫
    ((Functor.KInjectiveModel.fac (ordinary U)).app
      (((epsilonStar U).mapHomologicalComplex (ComplexShape.up ℤ)).obj A)).symm ≪≫
    (derived U).mapIso ((epsilonStar U).mapDerivedCategoryFactors.app A).symm

/-- The counit isomorphism uses the actual underived counit at the K-injective model and
reverses the specified original-input augmentation. -/
def counitOnInput (U : Over S) (E : CochainComplex (ofOver U).Modules ℤ)
    (hE : derivedQuasiCoherentModuleProperty (ofOver U) (DerivedCategory.Q.obj E)) :
    (derived U ⋙ epsilonStarDerived U).obj (DerivedCategory.Q.obj E) ≅
      DerivedCategory.Q.obj E :=
  (epsilonStarDerived U).mapIso ((Functor.KInjectiveModel.fac (ordinary U)).app E) ≪≫
    (epsilonStar U).mapDerivedCategoryFactors.app
      (((ordinary U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((CochainComplex.KInjectiveResolution.Construction.replacement.{u}
          (ofOver U).Modules).obj E)) ≪≫
    Localization.isoOfHom (DerivedCategory.Q (C := (ofOver U).Modules))
      (HomologicalComplex.quasiIso (ofOver U).Modules (ComplexShape.up ℤ))
      (counitOnCochains U E) (counitOnCochains_quasiIso U E hE) ≪≫
    (Functor.KInjectiveModel.inputAugmentationIso E).symm

/-- Exact inverse image preserves quasi-coherent cohomology. -/
theorem epsilonStarDerived_mapsTo (U : Over S) :
    Scheme.derivedQuasiCoherentModuleProperty U.left ≤
      (derivedQuasiCoherentModuleProperty (ofOver U)).inverseImage (epsilonStarDerived U) := sorry

/-- Derived direct image along the étale-to-Zariski morphism preserves quasi-coherent cohomology. -/
theorem derived_mapsTo (U : Over S) :
    derivedQuasiCoherentModuleProperty (ofOver U) ≤
      (Scheme.derivedQuasiCoherentModuleProperty U.left).inverseImage (derived U) := sorry

end SchemeRestriction

/-- The source-facing represented-scheme restriction is `Rε_*` on `D_QCoh`. -/
def spaceToSchemeDerived (U : Over S) : DerivedQCoh (ofOver U) ⥤ Scheme.DerivedQCoh U.left :=
  ObjectProperty.FullSubcategory.restrict (SchemeRestriction.derived U)
    (SchemeRestriction.derived_mapsTo U)

/-- Forgetting quasi-coherence retains the actual unbounded right-derived direct image. -/
def spaceToSchemeDerivedInclusionIso (U : Over S) :
    spaceToSchemeDerived U ⋙ Scheme.DerivedQCoh.inclusion U.left ≅
      inclusion (ofOver U) ⋙ SchemeRestriction.derived U :=
  ObjectProperty.FullSubcategory.restrict.compιIso (SchemeRestriction.derived U)
    (SchemeRestriction.derived_mapsTo U)

/-- The source's exact inverse image on complexes with quasi-coherent cohomology. -/
def schemeToSpaceDerived (U : Over S) : Scheme.DerivedQCoh U.left ⥤ DerivedQCoh (ofOver U) :=
  ObjectProperty.FullSubcategory.restrict (SchemeRestriction.epsilonStarDerived U)
    (SchemeRestriction.epsilonStarDerived_mapsTo U)

/-- The unit on a derived quasi-coherent object transports only through the native derived
localization's specified cochain representative. -/
def schemeRestrictionUnitComponent (U : Over S) (A : Scheme.DerivedQCoh U.left) :
    A ≅ (schemeToSpaceDerived U ⋙ spaceToSchemeDerived U).obj A :=
  ObjectProperty.isoMk _
    ((DerivedCategory.Q.objObjPreimageIso A.obj).symm ≪≫
      SchemeRestriction.unitOnInput U (DerivedCategory.Q.objPreimage A.obj)
        ((Scheme.derivedQuasiCoherentModuleProperty U.left).prop_of_iso
          (DerivedCategory.Q.objObjPreimageIso A.obj).symm A.property) ≪≫
      (SchemeRestriction.epsilonStarDerived U ⋙ SchemeRestriction.derived U).mapIso
        (DerivedCategory.Q.objObjPreimageIso A.obj))

/-- The actual localized unit is natural, independently of the localization's representatives. -/
theorem schemeRestrictionUnitComponent_naturality (U : Over S)
    {A B : Scheme.DerivedQCoh U.left} (a : A ⟶ B) :
    a ≫ (schemeRestrictionUnitComponent U B).hom =
      (schemeRestrictionUnitComponent U A).hom ≫
        (schemeToSpaceDerived U ⋙ spaceToSchemeDerived U).map a := sorry

/-- The counit transports the actual model counit and augmentation through the native derived
localization's cochain representative. -/
def schemeRestrictionCounitComponent (U : Over S) (E : DerivedQCoh (ofOver U)) :
    (spaceToSchemeDerived U ⋙ schemeToSpaceDerived U).obj E ≅ E :=
  ObjectProperty.isoMk _
    ((SchemeRestriction.derived U ⋙ SchemeRestriction.epsilonStarDerived U).mapIso
        (DerivedCategory.Q.objObjPreimageIso E.obj).symm ≪≫
      SchemeRestriction.counitOnInput U (DerivedCategory.Q.objPreimage E.obj)
        ((derivedQuasiCoherentModuleProperty (ofOver U)).prop_of_iso
          (DerivedCategory.Q.objObjPreimageIso E.obj).symm E.property) ≪≫
      DerivedCategory.Q.objObjPreimageIso E.obj)

/-- The actual localized counit is natural on the full derived quasi-coherent category. -/
theorem schemeRestrictionCounitComponent_naturality (U : Over S)
    {E F : DerivedQCoh (ofOver U)} (a : E ⟶ F) :
    (spaceToSchemeDerived U ⋙ schemeToSpaceDerived U).map a ≫
        (schemeRestrictionCounitComponent U F).hom =
      (schemeRestrictionCounitComponent U E).hom ≫ a := sorry

/-- Exact inverse image and the constructed right-derived restriction are inverse equivalences.
Both directions and the unit/counit maps are the displayed native cochain-localization data. -/
def schemeRestrictionEquivalence (U : Over S) :
    Scheme.DerivedQCoh U.left ≌ DerivedQCoh (ofOver U) where
  functor := schemeToSpaceDerived U
  inverse := spaceToSchemeDerived U
  unitIso := NatIso.ofComponents (schemeRestrictionUnitComponent U)
    (fun a ↦ schemeRestrictionUnitComponent_naturality U a)
  counitIso := NatIso.ofComponents (schemeRestrictionCounitComponent U)
    (fun a ↦ schemeRestrictionCounitComponent_naturality U a)
  functor_unitIso_comp := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
