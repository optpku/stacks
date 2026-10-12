/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap91.Lemma_91_10_4_Obstruction
public import stacks_project.Chap91.Remark_91_10_7
import Mathlib.Tactic.CrossRefAttribute

/-!
# Functoriality of existence obstructions along morphisms of first-order thickenings

After identifying underlying topoi, a morphism of first-order thickenings of (Sh(C), 𝒪)
induces an 𝒪-module map of kernel ideals, and Ext-postcomposition in the kernel variable
sends the existence obstruction of Lemma 91.10.4 on the source thickening to the obstruction
on the target.
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

/-- Remark 91.10.9: after identifying underlying topoi as in Remark 91.10.7, let
πᵢ : 𝒪'ᵢ ⟶ 𝒪 be first-order thickenings of (Sh(C), 𝒪) and let h : 𝒪'₂ ⟶ 𝒪'₁ be a
morphism of thickenings (source h : (Sh(D₁), 𝒪'₁) ⟶ (Sh(D₂), 𝒪'₂)), so h ≫ π₁ = π₂.
Lean h is source h^♯ and induces the 𝒪-module map ℐ₂ ⟶ ℐ₁. Given 𝒪-modules ℱ, 𝒦ᵢ,
maps cᵢ : ℐᵢ ⊗ ℱ ⟶ 𝒦ᵢ, and k : 𝒦₂ ⟶ 𝒦₁ making the c-square commute,
(Ext.mk₀ k).postcomp ℱ sends the existence obstruction o(ℱ, 𝒦₂, c₂) in Ext ℱ 𝒦₂ 2
to o(ℱ, 𝒦₁, c₁) in Ext ℱ 𝒦₁ 2. -/
@[stacks 0CYC]
theorem obstruction_postcomp {π1 : 𝒪1 ⟶ 𝒪} {π2 : 𝒪2 ⟶ 𝒪}
    [hπ1 : IsFirstOrderThickening π1] [hπ2 : IsFirstOrderThickening π2]
    [(SheafOfModules.restrictScalars (ringSheafMap π1)).IsRightAdjoint]
    [(SheafOfModules.restrictScalars (ringSheafMap π2)).IsRightAdjoint]
    [SheafOfModules.Localization.HasLowerShriek.{max u v} (ringSheaf J 𝒪1)]
    [SheafOfModules.Localization.HasLowerShriek.{max u v} (ringSheaf J 𝒪2)]
    {F K1 K2 : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    {c1 : moduleTensor (ideal π1) F ⟶ K1} {c2 : moduleTensor (ideal π2) F ⟶ K2}
    (h : 𝒪2 ⟶ 𝒪1) (h_comm : h ≫ π1 = π2) (k : K2 ⟶ K1)
    (hc : CommSq c2 (moduleTensorMap (idealMap h h_comm hπ1.isSquareZero hπ2.isSquareZero) (𝟙 F))
      k c1) :
    (Ext.mk₀ k).postcomp F (add_zero 2) (obstruction π2 F K2 c2) =
      obstruction π1 F K1 c1 := sorry

end ModuleExtension
end SheafOfModules.RingedSite.FirstOrderThickening
