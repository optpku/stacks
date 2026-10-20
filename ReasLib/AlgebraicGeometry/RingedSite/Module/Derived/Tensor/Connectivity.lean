/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Cohomology
public import ReasLib.CategoryTheory.DerivedCategory.Bounded

/-!
# Cohomological connectivity under derived tensor products

Derived tensoring with a module sheaf in degree zero preserves upper cohomological
isomorphism ranges, including the variant with an epimorphism at the boundary.
-/

@[expose] public section

open CategoryTheory DerivedCategory
open SheafOfModules.RingedSite (ringedSiteModuleCategory)
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u v w

namespace RingedSite.Hom.ModuleDerived

-- Local instance justification (defeq pin): `moduleCat_hasDerivedCategory` is reducible to
-- `HasDerivedCategory.standard` and is not global; `ModuleDerived`, `cohomologySheafMap`,
-- `IsBoundedAbove`, `singleFunctor`, and `DerivedTensor.Right.functor` must share that model.
-- `moduleCategoryHasDerivedCategory` unfolds to `moduleCat_hasDerivedCategory` at
-- `ofCommRingSheaf J O`; its site-indexed head lets instance synthesis recover J and O.
-- Local instance justification (defeq pin): the site-indexed standard model aligns ModuleDerived, cohomologySheafMap, singleFunctor, and derived tensoring while recovering J and O.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (O : Sheaf J CommRingCat.{w})

/-- The morphism obtained by derived tensoring with the identity of a module sheaf
placed in cohomological degree zero. -/
noncomputable abbrev tensorRightHom (F : ringedSiteModuleCategory.{u, v, w, w} J O)
    {K L : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)} (α : K ⟶ L) :
    K ⊗ᴸ (singleFunctor (ringedSiteModuleCategory.{u, v, w, w} J O) (0 : ℤ)).obj F ⟶
      L ⊗ᴸ (singleFunctor (ringedSiteModuleCategory.{u, v, w, w} J O) (0 : ℤ)).obj F :=
  (DerivedTensor.Right.functor
    ((singleFunctor (ringedSiteModuleCategory.{u, v, w, w} J O) (0 : ℤ)).obj F)).map α

/-- For a morphism between bounded-above derived module objects, derived tensoring with
a module sheaf preserves cohomological isomorphisms above an integer and an epimorphism
at that integer. -/
theorem derivedTensor_homologyMap_isIso_and_epi
    {K L : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)}
    (hK : IsBoundedAbove K) (hL : IsBoundedAbove L)
    (α : K ⟶ L) (F : ringedSiteModuleCategory.{u, v, w, w} J O) (n : ℤ)
    (hα_iso : ∀ j, n < j → IsIso (cohomologySheafMap (RingedSite.ofCommRingSheaf J O) j α))
    (hα_epi : Epi (cohomologySheafMap (RingedSite.ofCommRingSheaf J O) n α)) :
    (∀ i, n < i → IsIso (cohomologySheafMap (RingedSite.ofCommRingSheaf J O) i
      (tensorRightHom O F α))) ∧
      Epi (cohomologySheafMap (RingedSite.ofCommRingSheaf J O) n
        (tensorRightHom O F α)) := sorry

/-- For a morphism between bounded-above derived module objects, derived tensoring with
a module sheaf preserves cohomological isomorphisms in all degrees at least a given integer. -/
theorem derivedTensor_homologyMap_isIso
    {K L : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)}
    (hK : IsBoundedAbove K) (hL : IsBoundedAbove L)
    (α : K ⟶ L) (F : ringedSiteModuleCategory.{u, v, w, w} J O) (n : ℤ)
    (hα : ∀ j, n ≤ j → IsIso (cohomologySheafMap (RingedSite.ofCommRingSheaf J O) j α))
    (i : ℤ) (hi : n ≤ i) :
    IsIso (cohomologySheafMap (RingedSite.ofCommRingSheaf J O) i
      (tensorRightHom O F α)) := sorry

end RingedSite.Hom.ModuleDerived
