/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.AffineFppf
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.FlatBaseChange
public import ReasLib.AlgebraicGeometry.GroupoidsOver.RingedTopos
public import ReasLib.AlgebraicGeometry.RingedSite.Module.UniverseComparison
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfCocontinuous
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.GrothendieckLarge
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Category.Ring.FilteredColimits

/-! # Fppf direct images with enlarged coefficients

Coefficients and section carriers are enlarged to the universe containing the
objects of the site before forming direct images and injective resolutions.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor FiberedCategoryOver.Groupoids

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The two universe-lifted fppf coefficient sheaves are identified by identity
maps on their lifted section rings. -/
def fppfCoefficientIso (X : GroupoidsOver S) :
    SheafOfModules.UniverseLift.ring (ringedSite X).structureSheaf ≅
      (liftedFppfRingedSite X).structureSheaf :=
  (fullyFaithfulSheafToPresheaf (ringedSite X).siteTopology RingCat.{u + 1}).preimageIso
    (NatIso.ofComponents (fun _ => Iso.refl _) (by intros; ext x; rfl))

/-- Fppf modules lift by actual universe lifting of coefficients and sections,
followed by transport to the enlarged structure-sheaf presentation. -/
def fppfModuleUniverseLift (X : GroupoidsOver S) :
    fppfModules X ⥤ RingedSite.ModuleCat.{u + 1} (liftedFppfRingedSite X) :=
  SheafOfModules.UniverseLift.functor (ringedSite X).structureSheaf ⋙
    (SheafOfModules.CoefficientPresentation.equivalence (fppfCoefficientIso X)).functor

/-- Sections of a lifted fppf module are the universe lifts of its original sections. -/
theorem fppfModuleUniverseLift_carrier (X : GroupoidsOver S)
    (M : fppfModules X) (V : X.totalᵒᵖ) :
    (((fppfModuleUniverseLift X).obj M).val.obj V : Type (u + 1)) =
      ULift.{u + 1} (M.val.obj V) := rfl

/-- The canonical fppf coefficient comparison along a morphism lifts to the
enlarged structure sheaves. -/
def fppfCoefficientLiftIso {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    (toFunctor f).op ⋙ (liftedFppfRingedSite Y).structureSheaf.obj ≅
      (liftedFppfRingedSite X).structureSheaf.obj :=
  isoWhiskerLeft (toFunctor f).op
      ((sheafToPresheaf (ringedSite Y).siteTopology RingCat.{u + 1}).mapIso
        (fppfCoefficientIso Y)).symm ≪≫
    isoWhiskerRight
      ((sheafToPresheaf (ringedSite X).siteTopology RingCat.{u}).mapIso
        (associatedStructureSheafInverseImageIso f .fppf))
      SheafOfModules.UniverseLift.ringFunctor ≪≫
    (sheafToPresheaf (ringedSite X).siteTopology RingCat.{u + 1}).mapIso
      (fppfCoefficientIso X)

/-- A morphism of categories fibred in groupoids induces a morphism of fppf
ringed topoi with enlarged coefficients. -/
def fppfRingedToposHomLift {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    RingedSite.ToposHom (liftedFppfRingedSite X) (liftedFppfRingedSite Y) :=
  @RingedSite.Cocontinuous.toRingedTopos.{u + 1, u, u + 1, u, u + 1}
    (liftedFppfRingedSite X) (liftedFppfRingedSite Y) (toFunctor f)
    (toFunctor_isCocontinuous f .fppf) inferInstance
    (fun P V ↦ @HasLimitsOfShape.has_limit _ _ _ _ (by infer_instance)
      (StructuredArrow.proj V (toFunctor f).op ⋙ P))
    inferInstance inferInstance (fppfCoefficientLiftIso f).hom

/-- Direct image of fppf modules with coefficients in the universe containing
the objects of the site. -/
def fppfModuleDirectImageLift {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    RingedSite.ModuleCat.{u + 1} (liftedFppfRingedSite X) ⥤
      RingedSite.ModuleCat.{u + 1} (liftedFppfRingedSite Y) :=
  (fppfRingedToposHomLift f).modulePushforward

/-- Enlarged fppf direct image is pushforward along the canonical morphism of ringed topoi. -/
theorem fppfModuleDirectImageLift_eq {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    fppfModuleDirectImageLift f = (fppfRingedToposHomLift f).modulePushforward := rfl

/-- Enlarged fppf direct image is additive. -/
def fppfModuleDirectImageLift_additive {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    (fppfModuleDirectImageLift f).Additive :=
  RingedSite.ToposHom.modulePushforward_additive (fppfRingedToposHomLift f)

/-- Higher fppf direct image is the right derived functor of the actual
enlarged direct image, using large-site injective resolutions. -/
def fppfHigherDirectImageLiftFunctor {X Y : GroupoidsOver S} (f : X ⟶ Y) (i : ℕ) :
    RingedSite.ModuleCat.{u + 1} (liftedFppfRingedSite X) ⥤
      RingedSite.ModuleCat.{u + 1} (liftedFppfRingedSite Y) :=
  @CategoryTheory.Functor.rightDerived
    (RingedSite.ModuleCat.{u + 1} (liftedFppfRingedSite X)) _
    (RingedSite.ModuleCat.{u + 1} (liftedFppfRingedSite Y)) _
    (RingedSite.moduleCatAbelian.{u + 1, u + 1, u, u + 1} (liftedFppfRingedSite X))
    (SheafOfModules.LargeSite.injectiveResolutions.{u + 1, u}
      (ringedSite X).siteTopology (liftedFppfRingedSite X).structureSheaf)
    (RingedSite.moduleCatAbelian.{u + 1, u + 1, u, u + 1} (liftedFppfRingedSite Y))
    (fppfModuleDirectImageLift f) (fppfModuleDirectImageLift_additive f) i

/-- Bounded-below total fppf direct image is the right derived functor of
enlarged direct image, using the large-site enough-injectives certificate. -/
def fppfDerivedDirectImageLiftFunctor {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    DerivedCategory.Plus (RingedSite.ModuleCat.{u + 1} (liftedFppfRingedSite X)) ⥤
      DerivedCategory.Plus (RingedSite.ModuleCat.{u + 1} (liftedFppfRingedSite Y)) :=
  @CategoryTheory.Functor.rightDerivedFunctorPlus
    (RingedSite.ModuleCat.{u + 1} (liftedFppfRingedSite X))
    (RingedSite.ModuleCat.{u + 1} (liftedFppfRingedSite Y))
    _ _ _ _ _ _ (fppfModuleDirectImageLift f) (fppfModuleDirectImageLift_additive f)
    (SheafOfModules.LargeSite.enoughInjectives (ringedSite X).siteTopology
      (liftedFppfRingedSite X).structureSheaf)

/-- Bounded-below total fppf direct image computes the standard right derived
functor with the explicit additivity and large-site injectivity certificates. -/
theorem fppfDerivedDirectImageLiftFunctor_eq {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    fppfDerivedDirectImageLiftFunctor f =
      @CategoryTheory.Functor.rightDerivedFunctorPlus
        (RingedSite.ModuleCat.{u + 1} (liftedFppfRingedSite X))
        (RingedSite.ModuleCat.{u + 1} (liftedFppfRingedSite Y))
        _ _ _ _ _ _ (fppfModuleDirectImageLift f) (fppfModuleDirectImageLift_additive f)
        (SheafOfModules.LargeSite.enoughInjectives (ringedSite X).siteTopology
          (liftedFppfRingedSite X).structureSheaf) := rfl

end AlgebraicGeometry.GroupoidsOver
