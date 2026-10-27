/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.FirstOrderThickening.ExtMap
public import stacks_project.Chap91.Lemma_91_13_1_Obstruction

@[expose] public section
open CategoryTheory SheafOfModules.RingedSite SheafOfModules.RingedSite.NaiveCotangent
open scoped DerivedExt SheafOfModules.RingedSite
noncomputable section
universe u
namespace SheafOfModules.RingedSite.FirstOrderThickening
-- Local instance justification (defeq pin): `moduleCat_hasDerivedCategory` is reducible to `HasDerivedCategory.standard` and is not global; `ModuleDerived`, `singleFunctor`, and Ext must share that same derived-category instance.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
-- Local instance justification (defeq pin): the commutative-sheaf presentation uses the same standard derived-category owner, exposed through the site-level spelling.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O_B O_C O_D : Sheaf J CommRingCat.{u}}

variable {F : SheafOfModules (ringSheaf J O_C)}
variable {G : SheafOfModules (ringSheaf J O_D)}

/- Derived Ext¹ transport along a same-site coefficient map. -/
#check (SheafOfModules.RingedSite.FirstOrderThickening.extOne_map : ∀ {fSharp : O_B ⟶ O_C} {gSharp : O_C ⟶ O_D}
    (c : (extendAlong gSharp).obj F ⟶ G)
    (ξ :
      Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
        DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj F))),
    Ext⁽(1 : ℤ)⁾((SameSite.pullbackDerived gSharp).obj
        (DerivedCategory.Q.obj (NaiveCotangent.obj O_B (Under.mk fSharp))),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G)))

end SheafOfModules.RingedSite.FirstOrderThickening
