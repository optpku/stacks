/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.ChangeOfRings.Cochain
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.ChangeOfRings.Triangulated
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived

/-! # Tensor–Hom transport for Ext under change of rings -/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite
open scoped DerivedExt

noncomputable section

universe u

namespace SheafOfModules.RingedSite.SameSite

-- Local instance justification (defeq pin): the total derived functor and module localization use the standard module derived category.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
-- Local instance justification (defeq pin): the unbundled module category must use the same standard localization dictionary.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {R S : Sheaf J CommRingCat.{u}}

/-- The derived extension–restriction counit at a module concentrated in degree zero. -/
def counitToSingle (α : R ⟶ S) (G : SheafOfModules (ringSheaf J S)) :
    (pullbackDerived α).obj
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj
        ((restrictionAlong α).obj G))) ⟶
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G) :=
  (@Functor.LeftDerived.Homotopy.cochainCounit _ _ _ _ _ _ _ _
    ((sameSiteHom α).modulePullback) inferInstance
    (RingedSite.Hom.modulePullback.DerivedCategory.hasLeftDerived (sameSiteHom α))).app
      ((CochainComplex.singleFunctor _ 0).obj ((restrictionAlong α).obj G)) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
        ((sameSiteHom α).modulePullback) (ComplexShape.up ℤ) (0 : ℤ)).hom.app
          ((restrictionAlong α).obj G) ≫
        (CochainComplex.singleFunctor _ 0).map
          ((pullbackExtendIso α).hom.app ((restrictionAlong α).obj G) ≫
            (extendRestrictAdj α).counit.app G))

/-- Tensor–Hom transport sends a shifted morphism through derived extension and the counit. -/
def extRestrict (α : R ⟶ S) (X : DerivedCategory (ringedSiteModuleCategory J R))
    (G : SheafOfModules (ringSheaf J S)) (n : ℤ)
    (ξ : Ext⁽n⁾(X, DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor _ 0).obj ((restrictionAlong α).obj G)))) :
    Ext⁽n⁾((pullbackDerived α).obj X,
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G)) :=
  (pullbackDerived α).map ξ ≫
    ((pullbackDerived α).commShiftIso n).hom.app
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj
        ((restrictionAlong α).obj G))) ≫
    (shiftFunctor _ n).map (counitToSingle α G)

/-- Tensor–Hom transport is bijective in every integer degree for an arbitrary derived source. -/
theorem extRestrict_bijective (α : R ⟶ S)
    (X : DerivedCategory (ringedSiteModuleCategory J R))
    (G : SheafOfModules (ringSheaf J S)) (n : ℤ) :
    Function.Bijective (extRestrict α X G n) := sorry

/-- The tensor–Hom Ext equivalence for derived extension and restriction of scalars. -/
def extRestrictEquiv (α : R ⟶ S) (X : DerivedCategory (ringedSiteModuleCategory J R))
    (G : SheafOfModules (ringSheaf J S)) (n : ℤ) :
    Ext⁽n⁾(X, DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor _ 0).obj ((restrictionAlong α).obj G))) ≃
    Ext⁽n⁾((pullbackDerived α).obj X,
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G)) :=
  Equiv.ofBijective (extRestrict α X G n) (extRestrict_bijective α X G n)

/-- The forward tensor–Hom equivalence is the explicit derived-counit transport. -/
theorem extRestrictEquiv_apply (α : R ⟶ S)
    (X : DerivedCategory (ringedSiteModuleCategory J R))
    (G : SheafOfModules (ringSheaf J S)) (n : ℤ)
    (ξ : Ext⁽n⁾(X, DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor _ 0).obj ((restrictionAlong α).obj G)))) :
    extRestrictEquiv α X G n ξ = extRestrict α X G n ξ := sorry

end SheafOfModules.RingedSite.SameSite
