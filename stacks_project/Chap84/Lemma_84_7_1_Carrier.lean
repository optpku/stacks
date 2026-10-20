/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.UniverseLift
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Underlying

/-! # Carrier lift compatibility for module sheaves -/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace AlgebraicGeometry.AlgebraicSpace.AssociatedModule

/-- The carrier lift of a module sheaf with its coefficient sheaf unchanged. -/
abbrev moduleCarrierLift (site : RingedSite.{v, w, u})
    (moduleSheaf : RingedSite.ModuleCat.{u} site) :
    RingedSite.ModuleCat.{u + 1} site :=
  RingedSite.Module.carrierLift site moduleSheaf

#check (RingedSite.Module.carrierLift_obj :
  ∀ (site : RingedSite.{v, w, u}) (moduleSheaf : RingedSite.ModuleCat.{u} site)
    (siteObject : siteᵒᵖ),
    (RingedSite.Module.carrierLift site moduleSheaf).val.obj siteObject =
      (ModuleCat.uliftFunctor.{u + 1} _).obj (moduleSheaf.val.obj siteObject))

end AlgebraicGeometry.AlgebraicSpace.AssociatedModule

end

end
