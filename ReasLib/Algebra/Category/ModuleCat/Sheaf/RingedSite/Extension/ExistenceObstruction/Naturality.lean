/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Extension.ExistenceObstruction

/-!
# Naturality of the existence obstruction

A morphism of first-order thickenings and a compatible map of coefficient modules carry the
existence obstruction to the corresponding obstruction by postcomposition in Ext.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Abelian (Ext)
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.FirstOrderThickening

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.FirstOrderThickening
namespace ModuleExtension

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable {𝒪 𝒪1 𝒪2 : Sheaf J CommRingCat.{max u v}}
variable [HasExt.{w} (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)]
variable [HasFunctorialInjectives (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)]

/-- A compatible change of thickening and coefficient module carries the existence obstruction
to the corresponding Ext² class by postcomposition. -/
theorem obstruction_postcomp {π1 : 𝒪1 ⟶ 𝒪} {π2 : 𝒪2 ⟶ 𝒪}
    [hπ1 : IsFirstOrderThickening π1] [hπ2 : IsFirstOrderThickening π2]
    [(SheafOfModules.restrictScalars (ringSheafMap π1)).IsRightAdjoint]
    [(SheafOfModules.restrictScalars (ringSheafMap π2)).IsRightAdjoint]
    [SheafOfModules.Localization.HasLowerShriek.{max u v} (ringSheaf J 𝒪1)]
    [SheafOfModules.Localization.HasLowerShriek.{max u v} (ringSheaf J 𝒪2)]
    {F K1 K2 : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    {c1 : moduleTensor (ideal π1) F ⟶ K1} {c2 : moduleTensor (ideal π2) F ⟶ K2}
    (h : FirstOrderThickening.Hom π1 π2) (k : K2 ⟶ K1)
    (hc : CommSq c2 (moduleTensorMap h.idealMap (𝟙 F)) k c1) :
    (Ext.mk₀ k).postcomp F (add_zero 2) (existenceObstruction π2 F K2 c2) =
      existenceObstruction π1 F K1 c1 := sorry

end ModuleExtension
end SheafOfModules.RingedSite.FirstOrderThickening
