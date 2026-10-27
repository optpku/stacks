/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ModuleExtension.Trivial
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.FirstOrderThickening
open SheafOfModules.RingedSite.TrivSqZeroExt (splittingHomSnd)

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.FirstOrderThickening

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable {𝒪' 𝒪 : Sheaf J CommRingCat.{max u v}}

/- Restriction of scalars along a trivialization followed by restriction along π recovers the
original 𝒪-module, via σ ≫ π = 𝟙 𝒪. -/
#check (SheafOfModules.RingedSite.FirstOrderThickening.restrictEndpointIso :
    ∀ (π : 𝒪' ⟶ 𝒪) [IsFirstOrderThickening π]
    (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    (M : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪),
    (restrictionAlong σ).obj ((restrictionAlong π).obj M) ≅ M)

namespace ModuleExtension

/- The middle 𝒪'-module of the trivial 08MB extension: the additive sheaf of 𝒦 ⊞ ℱ
with the deformed splitting action. -/
#check (SheafOfModules.RingedSite.FirstOrderThickening.ModuleExtension.trivialModule :
    ∀ (π : 𝒪' ⟶ 𝒪) [IsFirstOrderThickening π]
    (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    (c : moduleTensor (ideal π) F ⟶ K),
    ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪')

/- The trivial 08MB extension of ℱ by 𝒦 corresponding to c and the trivialization σ. -/
#check (SheafOfModules.RingedSite.FirstOrderThickening.ModuleExtension.trivialExtension :
    ∀ (π : 𝒪' ⟶ 𝒪) [hπ : IsFirstOrderThickening π]
    (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    (c : moduleTensor (ideal π) F ⟶ K),
    ModuleExtension hπ.isSquareZero F K c)

/- The middle 𝒪'-module of the packaged trivial 08MB extension is `trivialModule`. -/
#check (SheafOfModules.RingedSite.FirstOrderThickening.ModuleExtension.trivialExtension_module :
    ∀ (π : 𝒪' ⟶ 𝒪) [hπ : IsFirstOrderThickening π]
    (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    (c : moduleTensor (ideal π) F ⟶ K),
    (trivialExtension π σ hσ c).module = trivialModule π σ hσ c)

end ModuleExtension

end SheafOfModules.RingedSite.FirstOrderThickening
