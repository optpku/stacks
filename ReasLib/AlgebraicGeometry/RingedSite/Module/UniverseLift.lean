/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic
public import Mathlib.Algebra.Category.ModuleCat.Ulift

@[expose] public section

open CategoryTheory

universe u v w

noncomputable section

namespace RingedSite.Module

/-- Objectwise carrier lift respects identity restriction with its scalar transport. -/
theorem carrierLiftPresheaf_map_id (site : RingedSite.{v, w, u})
    (moduleSheaf : RingedSite.ModuleCat.{u} site) (siteObject : site.carrierᵒᵖ) :
    (ModuleCat.uliftFunctor.{u + 1} _).map (moduleSheaf.val.map (𝟙 siteObject)) =
      (ModuleCat.restrictScalarsId' (site.structureSheaf.obj.map (𝟙 siteObject)).hom
        (congrArg RingCat.Hom.hom (site.structureSheaf.obj.map_id siteObject))).inv.app
          ((ModuleCat.uliftFunctor.{u + 1} _).obj (moduleSheaf.val.obj siteObject)) :=
  sorry

/-- Objectwise carrier lift respects composition of restrictions with its scalar transport. -/
theorem carrierLiftPresheaf_map_comp (site : RingedSite.{v, w, u})
    (moduleSheaf : RingedSite.ModuleCat.{u} site)
    {U V W : site.carrierᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    (ModuleCat.uliftFunctor.{u + 1} _).map (moduleSheaf.val.map (f ≫ g)) =
      (ModuleCat.uliftFunctor.{u + 1} _).map (moduleSheaf.val.map f) ≫
        (ModuleCat.restrictScalars (site.structureSheaf.obj.map f).hom).map
          ((ModuleCat.uliftFunctor.{u + 1} _).map (moduleSheaf.val.map g)) ≫
        (ModuleCat.restrictScalarsComp' (site.structureSheaf.obj.map f).hom
          (site.structureSheaf.obj.map g).hom (site.structureSheaf.obj.map (f ≫ g)).hom
          (congrArg RingCat.Hom.hom (site.structureSheaf.obj.map_comp f g))).inv.app
            ((ModuleCat.uliftFunctor.{u + 1} _).obj (moduleSheaf.val.obj W)) :=
  sorry

/-- Objectwise carrier lift of a module presheaf, leaving the coefficient sheaf unchanged. -/
def carrierLiftPresheaf (site : RingedSite.{v, w, u})
    (moduleSheaf : RingedSite.ModuleCat.{u} site) :
    _root_.PresheafOfModules.{u + 1} site.structureSheaf.obj where
  obj overScheme :=
    (ModuleCat.uliftFunctor.{u + 1} _).obj (moduleSheaf.val.obj overScheme)
  map restriction :=
    (ModuleCat.uliftFunctor.{u + 1} _).map (moduleSheaf.val.map restriction)
  map_id := carrierLiftPresheaf_map_id site moduleSheaf
  map_comp := carrierLiftPresheaf_map_comp site moduleSheaf

/-- Objectwise carrier lift preserves the sheaf condition. -/
theorem carrierLiftPresheaf_isSheaf (site : RingedSite.{v, w, u})
    (moduleSheaf : RingedSite.ModuleCat.{u} site) :
    Presheaf.IsSheaf site.siteTopology
      (carrierLiftPresheaf site moduleSheaf).presheaf := sorry

/-- Carrier lift of a module sheaf, with unchanged coefficient sheaf. -/
def carrierLift (site : RingedSite.{v, w, u})
    (moduleSheaf : RingedSite.ModuleCat.{u} site) :
    RingedSite.ModuleCat.{u + 1} site :=
  ⟨carrierLiftPresheaf site moduleSheaf,
    carrierLiftPresheaf_isSheaf site moduleSheaf⟩

/-- Evaluation of a carrier-lifted sheaf is the canonical module-carrier universe lift. -/
theorem carrierLift_obj (site : RingedSite.{v, w, u})
    (moduleSheaf : RingedSite.ModuleCat.{u} site) (siteObject : site.carrierᵒᵖ) :
    (carrierLift site moduleSheaf).val.obj siteObject =
      (ModuleCat.uliftFunctor.{u + 1} _).obj (moduleSheaf.val.obj siteObject) := rfl

end RingedSite.Module
