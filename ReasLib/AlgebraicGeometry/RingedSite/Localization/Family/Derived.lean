/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Family
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.LocallyGiven

/-!
# Derived slice components of a semi-representable family

The product decomposition `Mod(O_K) ≌ ∏ᵢ Mod(O_{U_i})` is inherited
by derived categories: restriction to the `i`-th slice is the exact derived functor of
`AtSR.component`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite
open RingedSite.Hom
open RingedSite.ModuleDerived
open scoped SemiRepresentableFamily

noncomputable section

universe ι u v w

namespace RingedSite.Localization.AtSR

variable {X : RingedSite.{u, v, w}}
variable [UnivLE.{max u v, w}] [UnivLE.{max ι u v, w}]
variable [X.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]

/-- Chosen derived-category structure on modules over `(C / K, O_K)`. -/
instance site_hasDerivedCategory (K : FormalCoproduct.{ι} X.carrier) :
    HasDerivedCategory (ModuleCat.{w} (site K)) :=
  moduleCat_hasDerivedCategory (site K)

/-- Slice restriction of modules on `(C / K, O_K)` is additive. -/
instance component_additive (K : FormalCoproduct.{ι} X.carrier) (i : K.I) :
    (component.{ι, u, v, w, w} K i).Additive := sorry

/-- Slice restriction of modules on `(C / K, O_K)` preserves finite limits. -/
instance component_preservesFiniteLimits (K : FormalCoproduct.{ι} X.carrier) (i : K.I) :
    PreservesFiniteLimits (component.{ι, u, v, w, w} K i) := sorry

/-- Slice restriction of modules on `(C / K, O_K)` preserves finite colimits. -/
instance component_preservesFiniteColimits (K : FormalCoproduct.{ι} X.carrier) (i : K.I) :
    PreservesFiniteColimits (component.{ι, u, v, w, w} K i) := sorry

/-- The bundled exact functor underlying slice restriction `Mod(O_K) ⥤ Mod(O_{U_i})`. -/
def componentExact (K : FormalCoproduct.{ι} X.carrier) (i : K.I) :
    ModuleCat.{w} (site K) ⥤ₑ ModuleCat.{w} (X.localization (K.obj i)) :=
  ⟨component.{ι, u, v, w, w} K i,
    ⟨component_preservesFiniteLimits K i, component_preservesFiniteColimits K i⟩⟩

/-- Restriction of an object of `D(O_K)` to the slice `D(O_{C / U_i})`. -/
def componentDerived (K : FormalCoproduct.{ι} X.carrier) (i : K.I) :
    Hom.ModuleDerived.{w} (site K) ⥤ Hom.ModuleDerived.{w} (X.localization (K.obj i)) :=
  (componentExact K i).mapDerivedCategory

/-- The product-decomposition functor on derived categories, sending an object of `D(O_K)`
to its family of slice restrictions in `∏ᵢ D(O_{U_i})`. -/
def derivedModulesEquivFunctor (K : FormalCoproduct.{ι} X.carrier) :
    Hom.ModuleDerived.{w} (site K) ⥤
      ∀ i : K.I, Hom.ModuleDerived.{w} (X.localization (K.obj i)) :=
  Functor.pi' fun i ↦ componentDerived K i

/-- Evaluation of the derived product-decomposition functor is slice restriction. -/
theorem derivedModulesEquiv_functor_obj (K : FormalCoproduct.{ι} X.carrier)
    (E : Hom.ModuleDerived.{w} (site K)) (i : K.I) :
    (derivedModulesEquivFunctor K).obj E i = (componentDerived K i).obj E :=
  rfl

/-- Natural form of `sliceInverseImageComparison`: restricting `j^*` to a slice recovers
`j_i^*`. -/
def sliceInverseImageNatIso (K : FormalCoproduct.{ι} X.carrier) (i : K.I) :
    Cocontinuous.moduleInverseImage (SemiRepresentableFamily.forget K) X.structureSheaf ⋙
        component.{ι, u, v, w, w} K i ≅
      Cocontinuous.moduleInverseImage (Over.forget (K.obj i)) X.structureSheaf :=
  NatIso.ofComponents (fun G ↦ sliceInverseImageComparison K i G) sorry

/-- The component of `sliceInverseImageNatIso` is `sliceInverseImageComparison`. -/
theorem sliceInverseImageNatIso_app (K : FormalCoproduct.{ι} X.carrier) (i : K.I)
    (G : SheafOfModules.{w} X.structureSheaf) :
    (sliceInverseImageNatIso K i).app G = sliceInverseImageComparison K i G := sorry

/-- Ambient restriction to `X.localization U` is geometric inverse image along `Over.forget U`. -/
def localizedRestrictionIsoInverseImage (U : X) :
    localizedRestriction.{w} X U ≅
      Cocontinuous.moduleInverseImage (Over.forget U) X.structureSheaf :=
  Iso.refl _

/-- The bundled exact functor underlying inverse image along an SR-morphism. -/
def mapModulePullbackExact {K L : FormalCoproduct.{ι} X.carrier} (φ : K ⟶ L) :
    ModuleCat.{w} (site L) ⥤ₑ ModuleCat.{w} (site K) :=
  ⟨mapModulePullback φ, map_modulePullback_exact φ⟩

/-- `mapModulePullbackExact` is the exact functor of `mapModulePullback`. -/
theorem mapModulePullbackExact_obj {K L : FormalCoproduct.{ι} X.carrier} (φ : K ⟶ L) :
    (mapModulePullbackExact φ).obj = mapModulePullback φ :=
  rfl

end RingedSite.Localization.AtSR
