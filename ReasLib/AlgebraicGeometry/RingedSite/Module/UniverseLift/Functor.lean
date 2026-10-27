/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.UniverseLift

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v w

namespace RingedSite.Module

/-- Objectwise carrier lift of a module-sheaf morphism commutes with restrictions. -/
theorem carrierLiftMap_naturality (site : RingedSite.{v, w, u})
    {F G : ModuleCat.{u} site} (f : F ⟶ G) {U V : site.carrierᵒᵖ} (i : U ⟶ V) :
    (carrierLift site F).val.map i ≫
        (ModuleCat.restrictScalars (site.structureSheaf.obj.map i).hom).map
          ((ModuleCat.uliftFunctor.{u + 1} _).map (f.val.app V)) =
      (ModuleCat.uliftFunctor.{u + 1} _).map (f.val.app U) ≫
        (carrierLift site G).val.map i := sorry

/-- A module-sheaf morphism lifted objectwise with unchanged coefficients. -/
def carrierLiftMap (site : RingedSite.{v, w, u})
    {F G : ModuleCat.{u} site} (f : F ⟶ G) :
    carrierLift site F ⟶ carrierLift site G :=
  ⟨{ app := fun U ↦ (ModuleCat.uliftFunctor.{u + 1} _).map (f.val.app U)
     naturality := carrierLiftMap_naturality site f }⟩

/-- Carrier lift of module-sheaf morphisms preserves identities. -/
theorem carrierLiftMap_id (site : RingedSite.{v, w, u}) (F : ModuleCat.{u} site) :
    carrierLiftMap site (𝟙 F) = 𝟙 (carrierLift site F) := sorry

/-- Carrier lift of module-sheaf morphisms preserves composition. -/
theorem carrierLiftMap_comp (site : RingedSite.{v, w, u})
    {F G H : ModuleCat.{u} site} (f : F ⟶ G) (g : G ⟶ H) :
    carrierLiftMap site (f ≫ g) = carrierLiftMap site f ≫ carrierLiftMap site g := sorry

/-- The objectwise carrier-universe lift as a functor on module sheaves. -/
def carrierLiftFunctor (site : RingedSite.{v, w, u}) :
    ModuleCat.{u} site ⥤ ModuleCat.{u + 1} site where
  obj := carrierLift site
  map := carrierLiftMap site
  map_id := carrierLiftMap_id site
  map_comp := carrierLiftMap_comp site

/-- The object map of the carrier-lift functor is the carrier lift of module sheaves. -/
theorem carrierLiftFunctor_obj (site : RingedSite.{v, w, u})
    (F : ModuleCat.{u} site) :
    (carrierLiftFunctor site).obj F = carrierLift site F :=
  rfl

/-- The morphism map of the carrier-lift functor is the objectwise lifted morphism. -/
theorem carrierLiftFunctor_map (site : RingedSite.{v, w, u})
    {F G : ModuleCat.{u} site} (f : F ⟶ G) :
    (carrierLiftFunctor site).map f = carrierLiftMap site f :=
  rfl

/-- Objectwise carrier lift is additive. -/
instance carrierLiftFunctor_additive (site : RingedSite.{v, w, u}) :
    (carrierLiftFunctor site).Additive := sorry

/-- Objectwise carrier lift preserves finite limits. -/
instance carrierLiftFunctor_preservesFiniteLimits (site : RingedSite.{v, w, u}) :
    PreservesFiniteLimits (carrierLiftFunctor site) := sorry

/-- Objectwise carrier lift preserves finite colimits. -/
instance carrierLiftFunctor_preservesFiniteColimits (site : RingedSite.{v, w, u}) :
    PreservesFiniteColimits (carrierLiftFunctor site) := sorry

end RingedSite.Module

end

end
