/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.FirstOrderThickening.Fiber
public import stacks_project.Chap91.Lemma_91_13_1_Obstruction

/-!
# Same-site tautological extension and coefficient map

The scalar-adjunction coefficient map and the original extension class are available
through the same-site fibre classification.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.FirstOrderThickening
open SheafOfModules.RingedSite.FirstOrderThickening.Solution
open SheafOfModules.RingedSite.NaiveCotangent
open scoped DerivedExt SheafOfModules.RingedSite

noncomputable section

universe u

namespace SheafOfModules.RingedSite.FirstOrderThickening
namespace Solution

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
variable {O_B' O_B O : Sheaf J CommRingCat.{u}}
variable (π : O_B' ⟶ O_B) [Sheaf.IsLocallySurjective π]
variable (hπ : KernelIdeal.IsSquareZero π)
variable (fSharp : O_B ⟶ O)
variable (G : SheafOfModules (ringSheaf J O))
variable (c :
    hπ.targetModule (KernelIdeal.quotientComparison_isIso π) ⟶
      (restrictionAlong fSharp).obj G)

#check (extendCoeff π hπ fSharp G c :
  (extendAlong fSharp).obj
    (hπ.targetModule (KernelIdeal.quotientComparison_isIso π)) ⟶ G)

#check (selfExtensionClass π hπ :
  Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (NaiveCotangent.obj O_B' (Under.mk π)),
    DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj
      (hπ.targetModule (KernelIdeal.quotientComparison_isIso π)))))

end Solution
end SheafOfModules.RingedSite.FirstOrderThickening
