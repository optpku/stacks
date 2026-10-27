/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ModuleExtension.ExtPushout
import StacksCheckRecall

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

/- Remark 91.10.8: after identifying underlying topoi, let πᵢ : 𝒪'ᵢ ⟶ 𝒪 be first-order
thickenings of (Sh(C), 𝒪) and let h : 𝒪'₂ ⟶ 𝒪'₁ be a morphism of thickenings (source
h : (Sh(D₁), 𝒪'₁) ⟶ (Sh(D₂), 𝒪'₂)), so h ≫ π₁ = π₂. Lean π is i^♯ and σ is the source
trivialization π^♯. Given trivializations σᵢ : 𝒪 ⟶ 𝒪'ᵢ with σ₂ ≫ h = σ₁ (source
π₁ = h ∘ π₂), 𝒪-modules ℱ, 𝒦ᵢ, maps cᵢ : ℐᵢ ⊗ ℱ ⟶ 𝒦ᵢ, and k : 𝒦₂ ⟶ 𝒦₁ making the
c-square commute, the Ext class from Remark 91.10.6 of the pushout from Remark 91.10.7
equals the Ext-postcomposition along k of the original Ext class. -/
@[stacks 08MK] #check
  (SheafOfModules.RingedSite.FirstOrderThickening.ModuleExtension.extClass_pushout :
    ∀ {π1 : 𝒪1 ⟶ 𝒪} {π2 : 𝒪2 ⟶ 𝒪}
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
    (F'2 : ModuleExtension hπ2.isSquareZero F K2 c2),
    extClass π1 σ1 hσ1 (Quotient.mk (isomorphicSetoid c1) (pushout h h_comm k hc F'2)) =
      (Ext.mk₀ k).postcomp F (add_zero 1)
        (extClass π2 σ2 hσ2 (Quotient.mk (isomorphicSetoid c2) F'2)))

end ModuleExtension
end SheafOfModules.RingedSite.FirstOrderThickening
