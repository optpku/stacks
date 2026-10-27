/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ModuleExtension.Trivialization
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
variable {𝒪' 𝒪 : Sheaf J CommRingCat.{max u v}}

/- Remark 91.10.6 (1): Let i : (Sh(C), 𝒪) ⟶ (Sh(D), 𝒪') be a trivial first-order thickening
of ringed topoi and let π : (Sh(D), 𝒪') ⟶ (Sh(C), 𝒪) be a trivialization. After identifying
underlying topoi, the Lean binder π : 𝒪' ⟶ 𝒪 is the thickening i^♯ and σ : 𝒪 ⟶ 𝒪' is the
chosen trivialization (source π^♯). Given 𝒪-modules ℱ, 𝒦 and c : ℐ ⊗ ℱ ⟶ 𝒦, the trivial
extension ℱ'_{c,triv} is the 08MB extension with underlying additive sheaf 𝒦 ⊞ ℱ (source
notation ℱ ⊕ 𝒦) and 𝒪'-action from the splitting associated to the trivialization together
with c. -/
@[stacks 08MI] #check (SheafOfModules.RingedSite.FirstOrderThickening.ModuleExtension.trivialExtension :
    ∀ (π : 𝒪' ⟶ 𝒪) [hπ : IsFirstOrderThickening π]
    (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    (c : moduleTensor (ideal π) F ⟶ K),
    ModuleExtension hπ.isSquareZero F K c)

variable [HasExt.{w} (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)]

/- Remark 91.10.6 (2): given any 08MB extension ℱ' with c = c_{ℱ'}, restriction of scalars
along π^♯ = σ lets one view ℱ' as an 𝒪-module extension, hence a class ξ_{ℱ'} in
Ext ℱ 𝒦 1. -/
@[stacks 08MI] #check (SheafOfModules.RingedSite.FirstOrderThickening.ModuleExtension.extClass :
    ∀ (π : 𝒪' ⟶ 𝒪) [hπ : IsFirstOrderThickening π]
    (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    {c : moduleTensor (ideal π) F ⟶ K} (E : IsoClass c),
    Ext F K 1)

/- Remark 91.10.6 (3): ℱ' ↦ ξ_{ℱ'} induces a bijection from isomorphism classes of 08MB
extensions with c = c_{ℱ'} to Ext ℱ 𝒦 1. -/
@[stacks 08MI] #check (SheafOfModules.RingedSite.FirstOrderThickening.ModuleExtension.extClass_bijective :
    ∀ (π : 𝒪' ⟶ 𝒪) [IsFirstOrderThickening π]
    (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    (c : moduleTensor (ideal π) F ⟶ K),
    Function.Bijective (extClass π σ hσ : IsoClass c → Ext F K 1))

/- Remark 91.10.6 (4): the trivial extension ℱ'_{c,triv} maps to the zero class. -/
@[stacks 08MI] #check (SheafOfModules.RingedSite.FirstOrderThickening.ModuleExtension.extClass_trivial :
    ∀ (π : 𝒪' ⟶ 𝒪) [IsFirstOrderThickening π]
    (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    (c : moduleTensor (ideal π) F ⟶ K),
    extClass π σ hσ (Quotient.mk (isomorphicSetoid c) (trivialExtension π σ hσ c)) = 0)

end ModuleExtension
end SheafOfModules.RingedSite.FirstOrderThickening
