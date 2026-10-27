/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Extension.ExistenceObstruction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ModuleExtension
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Abelian (Ext)
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
variable {𝒪' 𝒪 : Sheaf J CommRingCat.{max u v}}
variable [HasFunctorialInjectives (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)]

variable (π : 𝒪' ⟶ 𝒪)
variable [hπ : IsFirstOrderThickening π]
variable [(SheafOfModules.restrictScalars (ringSheafMap π)).IsRightAdjoint]
variable [SheafOfModules.Localization.HasLowerShriek.{max u v} (ringSheaf J 𝒪')]

variable [HasExt.{w} (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)]

/-- The canonical existence obstruction for a prescribed infinitesimal map. -/
noncomputable abbrev obstruction
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)
    (c : moduleTensor (ideal π) F ⟶ K) : Ext F K 2 :=
  existenceObstruction π F K c

/- The existence obstruction o(ℱ, 𝒦, c) ∈ Ext²_𝒪(ℱ, 𝒦). -/
#check (SheafOfModules.RingedSite.FirstOrderThickening.ModuleExtension.existenceObstruction π :
    ∀ (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)
    (c : moduleTensor (ideal π) F ⟶ K),
    Ext F K 2)

end ModuleExtension
end SheafOfModules.RingedSite.FirstOrderThickening
