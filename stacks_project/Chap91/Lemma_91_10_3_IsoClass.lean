/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ModuleExtension.IsoClass
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite

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
variable {𝒪' 𝒪 : Sheaf J CommRingCat.{max u v}} {π : 𝒪' ⟶ 𝒪}
variable [hπ : IsFirstOrderThickening π]
variable {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
variable {c : moduleTensor (ideal π) F ⟶ K}

/- The underlying fixed-endpoint extension of an 08MB mixed-scalar extension with prescribed
infinitesimal map, after restriction of scalars along π. -/
#check (SheafOfModules.RingedSite.FirstOrderThickening.ModuleExtension.toFixedEndpoint :
    ∀ (E : ModuleExtension hπ.isSquareZero F K c),
    CategoryTheory.Extension ((restrictionAlong π).obj K) ((restrictionAlong π).obj F))

/- Translate an 08MB extension with prescribed c by the restriction of an 𝒪-module extension,
using the Baer sum in Mod 𝒪'. -/
#check (SheafOfModules.RingedSite.FirstOrderThickening.ModuleExtension.vaddExtension :
    ∀ (ξ : CategoryTheory.Extension K F)
    (E : ModuleExtension hπ.isSquareZero F K c),
    ModuleExtension hπ.isSquareZero F K c)

/- The Baer-sum action computes on representatives. -/
#check (SheafOfModules.RingedSite.FirstOrderThickening.ModuleExtension.vadd_mk :
    ∀ (ξ : CategoryTheory.Extension K F)
    (E : ModuleExtension hπ.isSquareZero F K c),
    vadd (Quotient.mk (isIsomorphicSetoid (CategoryTheory.Extension K F)) ξ)
      (Quotient.mk (isomorphicSetoid c) E) =
      Quotient.mk (isomorphicSetoid c) (vaddExtension ξ E))

/- If at least one 08MB extension with prescribed c exists, then isomorphism classes form a
principal homogeneous space under the 𝒪-module extension group. -/
#check (SheafOfModules.RingedSite.FirstOrderThickening.ModuleExtension.existsUnique_vadd :
    ∀ (h_exists : Nonempty (ModuleExtension hπ.isSquareZero F K c))
    (E E' : IsoClass c),
    ∃! ξ : ExtensionClass K F, vadd ξ E = E')

end ModuleExtension
end SheafOfModules.RingedSite.FirstOrderThickening
