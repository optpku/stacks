/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.UniverseComparison
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.DirectImage
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.GrothendieckLarge
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfCocontinuous
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# Étale higher direct images with enlarged coefficients

Original-coefficient modules are explicitly lifted before taking injective
resolutions. The coefficient universe contains the objects of the étale site.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open FiberedCategoryOver.Groupoids

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Continuous precomposition identifies the target structure sheaf with the
source structure sheaf along a morphism of categories fibred in groupoids. -/
def etaleCoefficientIso {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    (toFunctor f).op ⋙ (etaleStructureSheaf Y).obj ≅ (etaleStructureSheaf X).obj :=
  (sheafToPresheaf X.etaleTopology RingCat.{u}).mapIso
    ((inverseImageEtaleStructureSheafIso f).symm ≪≫
      (sheafCompose X.etaleTopology (forget₂ CommRingCat.{u} RingCat.{u})).mapIso
        (commEtaleStructureSheafIso f))

/-- The canonical structure-sheaf comparison with enlarged coefficients is
obtained by lifting the original comparison and transporting coefficients. -/
def etaleCoefficientLiftIso {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    (toFunctor f).op ⋙ (commEtaleRingedSiteLift Y).structureSheaf.obj ≅
      (commEtaleRingedSiteLift X).structureSheaf.obj :=
  isoWhiskerLeft (toFunctor f).op
      ((sheafToPresheaf Y.etaleTopology RingCat.{u + 1}).mapIso
        (ModuleUniverseComparison.coefficientIso Y)).symm ≪≫
    isoWhiskerRight (etaleCoefficientIso f) SheafOfModules.UniverseLift.ringFunctor ≪≫
    (sheafToPresheaf X.etaleTopology RingCat.{u + 1}).mapIso
      (ModuleUniverseComparison.coefficientIso X)

/-- The forward and inverse enlarged coefficient comparisons compose to the identity. -/
theorem etaleCoefficientLiftIso_hom_inv_id {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    (etaleCoefficientLiftIso f).hom ≫ (etaleCoefficientLiftIso f).inv = 𝟙 _ :=
  (etaleCoefficientLiftIso f).hom_inv_id

/-- The inverse and forward enlarged coefficient comparisons compose to the identity. -/
theorem etaleCoefficientLiftIso_inv_hom_id {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    (etaleCoefficientLiftIso f).inv ≫ (etaleCoefficientLiftIso f).hom = 𝟙 _ :=
  (etaleCoefficientLiftIso f).inv_hom_id

/-- A morphism of categories fibred in groupoids induces the canonical morphism
of étale ringed topoi with enlarged coefficients. -/
def etaleRingedToposHomLift {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    RingedSite.ToposHom (commEtaleRingedSiteLift X) (commEtaleRingedSiteLift Y) :=
  @RingedSite.Cocontinuous.toRingedTopos.{u + 1, u, u + 1, u, u + 1}
    (commEtaleRingedSiteLift X) (commEtaleRingedSiteLift Y) (toFunctor f)
    (toFunctor_isCocontinuous_etale f) inferInstance
    (fun P V ↦ @HasLimitsOfShape.has_limit _ _ _ _ (by infer_instance)
      (StructuredArrow.proj V (toFunctor f).op ⋙ P))
    inferInstance inferInstance (etaleCoefficientLiftIso f).hom

/-- Étale direct image on the full category of enlarged-coefficient modules. -/
def etaleModuleDirectImageLift {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    EtaleModulesLift X ⥤ EtaleModulesLift Y :=
  (etaleRingedToposHomLift f).modulePushforward

/-- Enlarged-coefficient étale direct image is pushforward along the canonical
morphism of enlarged ringed topoi. -/
theorem etaleModuleDirectImageLift_eq {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    etaleModuleDirectImageLift f = (etaleRingedToposHomLift f).modulePushforward := rfl

/-- Étale direct image with enlarged coefficients is additive. -/
def etaleModuleDirectImageLift_additive {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    (etaleModuleDirectImageLift f).Additive :=
  RingedSite.ToposHom.modulePushforward_additive (etaleRingedToposHomLift f)

/-- Continuous precomposition with the inverse structure-sheaf comparison gives
the inverse-direction morphism of enlarged étale ringed sites. -/
def etaleSiteHomLift {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    RingedSite.Hom (commEtaleRingedSiteLift Y) (commEtaleRingedSiteLift X) where
  base := toFunctor f
  isMorphismOfSites := toFunctor_isMorphismOfSites_etale f
  structureSheafMap := ⟨(etaleCoefficientLiftIso f).inv⟩

/-- Étale inverse image with enlarged coefficients is continuous precomposition
with scalar restriction along the inverse canonical structure-sheaf comparison. -/
def etaleModuleInverseImageLift {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    EtaleModulesLift Y ⥤ EtaleModulesLift X :=
  (etaleSiteHomLift f).modulePushforward.{u + 1}

/-- Enlarged-coefficient inverse image is continuous module pushforward along
the inverse-direction morphism of ringed sites. -/
theorem etaleModuleInverseImageLift_eq {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    etaleModuleInverseImageLift f = (etaleSiteHomLift f).modulePushforward.{u + 1} := rfl

/-- The degree-`i` étale higher direct image on all enlarged-coefficient modules
uses injective resolutions at the universe containing the objects of the site. -/
def etaleHigherDirectImageLiftFunctor {X Y : GroupoidsOver S} (f : X ⟶ Y) (i : ℕ) :
    EtaleModulesLift X ⥤ EtaleModulesLift Y :=
  @CategoryTheory.Functor.rightDerived
    (RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X)) _
    (RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift Y)) _
    (RingedSite.moduleCatAbelian.{u + 1, u + 1, u, u + 1} (commEtaleRingedSiteLift X))
    (SheafOfModules.LargeSite.injectiveResolutions.{u + 1, u} X.etaleTopology
      (commEtaleRingedSiteLift X).structureSheaf)
    (RingedSite.moduleCatAbelian.{u + 1, u + 1, u, u + 1} (commEtaleRingedSiteLift Y))
    (etaleModuleDirectImageLift f) (etaleModuleDirectImageLift_additive f) i

/-- The enlarged étale higher direct image is the right derived direct image
computed using the canonical large-site injective resolutions. -/
theorem etaleHigherDirectImageLiftFunctor_eq {X Y : GroupoidsOver S} (f : X ⟶ Y) (i : ℕ) :
    etaleHigherDirectImageLiftFunctor f i =
      @CategoryTheory.Functor.rightDerived
        (RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X)) _
        (RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift Y)) _
        (RingedSite.moduleCatAbelian.{u + 1, u + 1, u, u + 1} (commEtaleRingedSiteLift X))
        (SheafOfModules.LargeSite.injectiveResolutions.{u + 1, u} X.etaleTopology
          (commEtaleRingedSiteLift X).structureSheaf)
        (RingedSite.moduleCatAbelian.{u + 1, u + 1, u, u + 1} (commEtaleRingedSiteLift Y))
        (etaleModuleDirectImageLift f) (etaleModuleDirectImageLift_additive f) i := rfl

/-- The degree-`i` higher direct image of an enlarged-coefficient étale module. -/
abbrev etaleHigherDirectImageLift {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (F : EtaleModulesLift X) (i : ℕ) : EtaleModulesLift Y :=
  (etaleHigherDirectImageLiftFunctor f i).obj F

/-- Higher direct image of an enlarged-coefficient module is the object map of
the full-domain higher-direct-image functor. -/
theorem etaleHigherDirectImageLift_eq {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (F : EtaleModulesLift X) (i : ℕ) :
    etaleHigherDirectImageLift f F i = (etaleHigherDirectImageLiftFunctor f i).obj F := rfl

/-- The degree-`i` étale higher direct image on original-coefficient inputs.
The input is explicitly lifted, and resolutions and outputs have coefficients
in the universe containing the objects of the site. -/
def moduleHigherDirectImageFunctor {X Y : GroupoidsOver S} (f : X ⟶ Y) (i : ℕ) :
    etaleModules X ⥤ EtaleModulesLift Y :=
  ModuleUniverseComparison.lift X ⋙ etaleHigherDirectImageLiftFunctor f i

/-- The degree-`i` étale higher direct image of a module, computed after
explicitly lifting its coefficients to the universe containing the site. -/
abbrev moduleHigherDirectImage {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (F : etaleModules X) (i : ℕ) : EtaleModulesLift Y :=
  (moduleHigherDirectImageFunctor f i).obj F

/-- Higher direct image of a module is the object map of the higher-direct-image functor. -/
theorem moduleHigherDirectImage_eq {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (F : etaleModules X) (i : ℕ) :
    moduleHigherDirectImage f F i = (moduleHigherDirectImageFunctor f i).obj F :=
  rfl

/-- Bounded-below total étale direct image is the right derived functor of
enlarged direct image, using the large-site enough-injectives certificate. -/
def etaleDerivedDirectImageLiftFunctor {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    DerivedCategory.Plus (EtaleModulesLift X) ⥤ DerivedCategory.Plus (EtaleModulesLift Y) :=
  @CategoryTheory.Functor.rightDerivedFunctorPlus
    (EtaleModulesLift X) (EtaleModulesLift Y)
    _ _ _ _ _ _ (etaleModuleDirectImageLift f) (etaleModuleDirectImageLift_additive f)
    (SheafOfModules.LargeSite.enoughInjectives X.etaleTopology
      (commEtaleRingedSiteLift X).structureSheaf)

/-- Bounded-below total étale direct image computes the standard right derived
functor with the explicit additivity and large-site injectivity certificates. -/
theorem etaleDerivedDirectImageLiftFunctor_eq {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    etaleDerivedDirectImageLiftFunctor f =
      @CategoryTheory.Functor.rightDerivedFunctorPlus
        (EtaleModulesLift X) (EtaleModulesLift Y)
        _ _ _ _ _ _ (etaleModuleDirectImageLift f) (etaleModuleDirectImageLift_additive f)
        (SheafOfModules.LargeSite.enoughInjectives X.etaleTopology
          (commEtaleRingedSiteLift X).structureSheaf) := rfl

end AlgebraicGeometry.GroupoidsOver
