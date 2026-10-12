/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic

/-!
# Carrier universe lift of module sheaves

Objectwise `ModuleCat.uliftFunctor` raises the carrier universe of a module
sheaf by one while leaving the coefficient sheaf unchanged. This supplies the
size condition needed for higher direct images on algebraic-space sites.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w z

namespace AlgebraicGeometry.AlgebraicSpace.AssociatedModule

/-- Objectwise carrier lift of a module presheaf, leaving the coefficient sheaf
unchanged. -/
def moduleCarrierLiftPresheaf (site : RingedSite.{v, w, u})
    (moduleSheaf : RingedSite.ModuleCat.{u} site) :
    _root_.PresheafOfModules.{u + 1} site.structureSheaf.obj where
  obj siteObject :=
    (ModuleCat.uliftFunctor.{u + 1} _).obj (moduleSheaf.val.obj siteObject)
  map restriction :=
    (ModuleCat.uliftFunctor.{u + 1} _).map (moduleSheaf.val.map restriction)
  map_id := sorry
  map_comp := sorry

/-- Evaluation of the carrier-lifted presheaf is the canonical module-carrier
universe lift. -/
theorem moduleCarrierLiftPresheaf_obj (site : RingedSite.{v, w, u})
    (moduleSheaf : RingedSite.ModuleCat.{u} site) (siteObject : siteᵒᵖ) :
    (moduleCarrierLiftPresheaf site moduleSheaf).obj siteObject =
      (ModuleCat.uliftFunctor.{u + 1} _).obj (moduleSheaf.val.obj siteObject) :=
  rfl

/-- Objectwise carrier lift preserves the sheaf condition. -/
theorem moduleCarrierLiftPresheaf_isSheaf (site : RingedSite.{v, w, u})
    (moduleSheaf : RingedSite.ModuleCat.{u} site) :
    Presheaf.IsSheaf site.siteTopology
      (moduleCarrierLiftPresheaf site moduleSheaf).presheaf :=
  sorry

/-- Carrier lift of a module sheaf, with unchanged coefficient sheaf. -/
def moduleCarrierLift (site : RingedSite.{v, w, u})
    (moduleSheaf : RingedSite.ModuleCat.{u} site) :
    RingedSite.ModuleCat.{u + 1} site :=
  ⟨moduleCarrierLiftPresheaf site moduleSheaf,
    moduleCarrierLiftPresheaf_isSheaf site moduleSheaf⟩

/-- Evaluation of a carrier-lifted sheaf is the canonical module-carrier universe
lift. -/
theorem moduleCarrierLift_obj (site : RingedSite.{v, w, u})
    (moduleSheaf : RingedSite.ModuleCat.{u} site) (siteObject : siteᵒᵖ) :
    (moduleCarrierLift site moduleSheaf).val.obj siteObject =
      (ModuleCat.uliftFunctor.{u + 1} _).obj (moduleSheaf.val.obj siteObject) :=
  rfl

/-- The underlying abelian-group presheaf of a module sheaf. -/
def underlyingAbPresheaf (site : RingedSite.{v, w, u})
    (moduleSheaf : RingedSite.ModuleCat.{z} site) :
    siteᵒᵖ ⥤ AddCommGrpCat.{z} :=
  (SheafOfModules.forget.{z} site.structureSheaf ⋙
    PresheafOfModules.toPresheaf.{z} site.structureSheaf.obj).obj moduleSheaf

/-- Evaluating the underlying abelian-group presheaf recovers the abelian
presheaf of the module sheaf. -/
theorem underlyingAbPresheaf_obj (site : RingedSite.{v, w, u})
    (moduleSheaf : RingedSite.ModuleCat.{z} site) (siteObject : siteᵒᵖ) :
    (underlyingAbPresheaf site moduleSheaf).obj siteObject =
      moduleSheaf.val.presheaf.obj siteObject :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.AssociatedModule

end

end
