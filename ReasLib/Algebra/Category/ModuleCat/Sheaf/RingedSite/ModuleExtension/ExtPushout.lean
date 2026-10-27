/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ModuleExtension.Trivialization
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ModuleExtension.Pushout

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

/-- For compatible trivializations and a commuting square of prescribed infinitesimal maps,
the Ext¹ class of the canonical pushout of a module extension is the postcomposition
of its original Ext¹ class along the coefficient map. -/
theorem extClassOn_pushout {π1 : 𝒪1 ⟶ 𝒪} {π2 : 𝒪2 ⟶ 𝒪}
    [hπ1 : IsFirstOrderThickening π1] [hπ2 : IsFirstOrderThickening π2]
    (σ1 : 𝒪 ⟶ 𝒪1) (σ2 : 𝒪 ⟶ 𝒪2)
    (hσ1 : IsTrivialization σ1 π1) (hσ2 : IsTrivialization σ2 π2)
    {F K1 K2 : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    {c1 : moduleTensor (ideal π1) F ⟶ K1} {c2 : moduleTensor (ideal π2) F ⟶ K2}
    (h : 𝒪2 ⟶ 𝒪1) (h_comm : h ≫ π1 = π2) (hσ_comm : σ2 ≫ h = σ1)
    (k : K2 ⟶ K1)
    (hc : CommSq c2
      (moduleTensorMap
        (KernelIdeal.IsSquareZero.mapToTarget h h_comm hπ1.isSquareZero hπ2.isSquareZero) (𝟙 F))
      k c1)
    (F'2 : ModuleExtension hπ2.isSquareZero F K2 c2) :
    extClassOn π1 σ1 hσ1 (pushout h h_comm k hc F'2) =
      (Ext.mk₀ k).postcomp F (add_zero 1) (extClassOn π2 σ2 hσ2 F'2) := sorry

/-- For compatible trivializations and a commuting square of prescribed infinitesimal maps,
the Ext¹ class of the isomorphism class of the canonical pushout is the postcomposition
of the original Ext¹ class along the coefficient map. -/
theorem extClass_pushout {π1 : 𝒪1 ⟶ 𝒪} {π2 : 𝒪2 ⟶ 𝒪}
    [hπ1 : IsFirstOrderThickening π1] [hπ2 : IsFirstOrderThickening π2]
    (σ1 : 𝒪 ⟶ 𝒪1) (σ2 : 𝒪 ⟶ 𝒪2)
    (hσ1 : IsTrivialization σ1 π1) (hσ2 : IsTrivialization σ2 π2)
    {F K1 K2 : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    {c1 : moduleTensor (ideal π1) F ⟶ K1} {c2 : moduleTensor (ideal π2) F ⟶ K2}
    (h : 𝒪2 ⟶ 𝒪1) (h_comm : h ≫ π1 = π2) (hσ_comm : σ2 ≫ h = σ1)
    (k : K2 ⟶ K1)
    (hc : CommSq c2
      (moduleTensorMap
        (KernelIdeal.IsSquareZero.mapToTarget h h_comm hπ1.isSquareZero hπ2.isSquareZero) (𝟙 F))
      k c1)
    (F'2 : ModuleExtension hπ2.isSquareZero F K2 c2) :
    extClass π1 σ1 hσ1 (Quotient.mk (isomorphicSetoid c1) (pushout h h_comm k hc F'2)) =
      (Ext.mk₀ k).postcomp F (add_zero 1)
        (extClass π2 σ2 hσ2 (Quotient.mk (isomorphicSetoid c2) F'2)) := sorry

end ModuleExtension
end SheafOfModules.RingedSite.FirstOrderThickening
