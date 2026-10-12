/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic
public import Mathlib.Algebra.Category.ModuleCat.Ulift

@[expose] public section

open CategoryTheory

universe u v w

noncomputable section

namespace RingedSite.Module

/-- Objectwise carrier lift of a module presheaf, leaving the coefficient sheaf unchanged. -/
def carrierLiftPresheaf (site : RingedSite.{v, w, u})
    (moduleSheaf : RingedSite.ModuleCat.{u} site) :
    _root_.PresheafOfModules.{u + 1} site.structureSheaf.obj where
  obj overScheme :=
    (ModuleCat.uliftFunctor.{u + 1} _).obj (moduleSheaf.val.obj overScheme)
  map restriction :=
    (ModuleCat.uliftFunctor.{u + 1} _).map (moduleSheaf.val.map restriction)
  map_id := sorry
  map_comp := sorry

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
    (moduleSheaf : RingedSite.ModuleCat.{u} site) (siteObject : siteᵒᵖ) :
    (carrierLift site moduleSheaf).val.obj siteObject =
      (ModuleCat.uliftFunctor.{u + 1} _).obj (moduleSheaf.val.obj siteObject) := sorry

end RingedSite.Module
