/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic

@[expose] public section

/-!
# Localized derived module categories on ringed sites

This module provides the site-presented spelling of the derived category of module sheaves and
the exact derived functor induced by restriction to a localized ringed site.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u v w z


namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J CommRingCat.{w}}

/-- The site-presented module category inherits the canonical abelian structure from its bundled
ringed site. -/
@[reducible]
noncomputable def moduleCategoryAbelian
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [UnivLE.{max u v, z}] :
    Abelian (ringedSiteModuleCategory.{u, v, z, w} J 𝒪) :=
  _root_.RingedSite.moduleCatAbelian.{z} (RingedSite.ofCommRingSheaf J 𝒪)

/-- The site-presented module category uses the canonical derived-category structure of the
associated bundled ringed site. -/
@[reducible]
noncomputable def moduleCategoryHasDerivedCategory
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [UnivLE.{max u v, z}] :
    HasDerivedCategory.{max (max (max u v) w) (z + 1)}
      (ringedSiteModuleCategory.{u, v, z, w} J 𝒪) :=
  RingedSite.Hom.moduleCat_hasDerivedCategory.{z}
    (RingedSite.ofCommRingSheaf J 𝒪)

/-- The unbounded derived category `D(𝒪)` of sheaves of `𝒪`-modules on the ringed site
`(C, J)`. -/
abbrev RingedSiteDerived (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (𝒪 : Sheaf J CommRingCat.{w}) [UnivLE.{max u v, z}] :=
  _root_.RingedSite.Hom.ModuleDerived.{z} (RingedSite.ofCommRingSheaf J 𝒪)

namespace RingedSiteDerived

/-- The canonical max-universe derived category attached to a commutative ring-sheaf
presentation. -/
@[stacks 09LX "max-universe derived-category presentation for tensoring"]
abbrev max (J : GrothendieckTopology C)
    (𝒪 : Sheaf J CommRingCat.{max u v}) :=
  @_root_.RingedSite.Hom.ModuleDerived.{max u v, u, v, max u v}
    (_root_.RingedSite.ofCommSheafMax J 𝒪) UnivLE.self

end RingedSiteDerived

end

end SheafOfModules.RingedSite

namespace RingedSite.Hom

section LocalizedModuleCategory

variable {X : RingedSite.{u, v, w}} (U : X.carrier)
variable [UnivLE.{max u v, z}]

/-- The localized module category has the canonical abelian structure of a ringed-site module
category. -/
@[stacks 08FJ "abelian structure on localized ringed-site modules", reducible]
noncomputable def localizedModuleCatAbelian :
    Abelian (ModuleCat.{z} (X.localization U)) :=
  RingedSite.moduleCatAbelian (X.localization U)

/-- The localized module category carries its standard derived-category structure. -/
@[stacks 08FJ "derived category on localized ringed-site modules", reducible]
noncomputable def localizedModuleCatHasDerivedCategory :
    HasDerivedCategory (ModuleCat.{z} (X.localization U)) :=
  RingedSite.Hom.moduleCat_hasDerivedCategory (X.localization U)

end LocalizedModuleCategory

/-- Sheafification on an equiverse localized ringed site is inherited from its over-site
topology. -/
theorem localizedModuleCatHasSheafify
    {X : RingedSite.{u, u, u}} (U : X.carrier) :
    HasSheafify (X.siteTopology.over U) AddCommGrpCat.{u} := by
  infer_instance

/-- Ext groups on an equiverse localized ringed site use the small model supplied by its
Grothendieck abelian module category. -/
theorem localizedModuleCatHasExt
    {X : RingedSite.{u, u, u}} (U : X.carrier)
    [(X.siteTopology.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    HasExt.{u} (ModuleCat.{u} (X.localization U)) :=
  @IsGrothendieckAbelian.hasExt _ inferInstance
    (localizedModuleCatAbelian U)
    (@SheafOfModules.isGrothendieckAbelian _ inferInstance _
      (localizedModuleCatHasSheafify U) inferInstance
      (X.localization U).structureSheaf)

/-- The exact functor on derived categories induced by restricting module sheaves to the
localized ringed site `(X/U, 𝒪_U)`. -/
abbrev localizedRestrictionDerived.{z', u', v', w'}
    (X : _root_.RingedSite.{u', v', w'}) (U : X.carrier)
    [UnivLE.{max u' v', z'}] :
    ModuleDerived.{z'} X ⥤ ModuleDerived.{z'} (X.localization U) :=
  @CategoryTheory.Functor.mapDerivedCategory
    (ModuleCat.{z'} X) inferInstance inferInstance (moduleCat_hasDerivedCategory X)
    (ModuleCat.{z'} (X.localization U)) inferInstance (localizedModuleCatAbelian U)
      (localizedModuleCatHasDerivedCategory U)
    (localizedRestriction.{z'} X U) inferInstance inferInstance inferInstance

namespace RingedSiteDerived

/-- Notation for the localized derived inverse-image functor `j_U⁻¹`. -/
scoped notation:max "j[" U:max "]⁻¹" =>
  RingedSite.Hom.localizedRestrictionDerived _ U

end RingedSiteDerived

end RingedSite.Hom
