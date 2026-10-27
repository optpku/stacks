/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ModuleExtension.Trivialization
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
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
variable {𝒪' 𝒪 : Sheaf J CommRingCat.{max u v}}

/- Restriction of scalars along a trivialization turns an 08MB mixed-scalar extension into
an 𝒪-module extension of ℱ by 𝒦, after identifying the endpoints via σ ≫ π = 𝟙 𝒪. -/
#check (SheafOfModules.RingedSite.FirstOrderThickening.ModuleExtension.restrictScalarsExtension :
    ∀ (π : 𝒪' ⟶ 𝒪)
    [hπ : IsFirstOrderThickening π] (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    {c : moduleTensor (ideal π) F ⟶ K}
    (E : ModuleExtension hπ.isSquareZero F K c),
    CategoryTheory.Extension K F)

/- The principal-homogeneous-space chart sending an 08MB isomorphism class to its 𝒪-module
extension class along σ, with inverse the Baer translate of the trivial extension. -/
#check (SheafOfModules.RingedSite.FirstOrderThickening.ModuleExtension.isoClassExtensionClassEquiv :
    ∀ (π : 𝒪' ⟶ 𝒪)
    [hπ : IsFirstOrderThickening π] (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    (c : moduleTensor (ideal π) F ⟶ K),
    IsoClass c ≃ ExtensionClass K F)

variable [HasExt.{w} (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)]

/- The Ext¹ class of an 08MB extension, as an 𝒪-module extension via the trivialization. -/
#check (SheafOfModules.RingedSite.FirstOrderThickening.ModuleExtension.extClassOn :
    ∀ (π : 𝒪' ⟶ 𝒪)
    [hπ : IsFirstOrderThickening π] (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    {c : moduleTensor (ideal π) F ⟶ K}
    (E : ModuleExtension hπ.isSquareZero F K c),
    Ext F K 1)

end ModuleExtension
end SheafOfModules.RingedSite.FirstOrderThickening
