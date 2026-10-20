/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Coextension

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.DerivedCoextension

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat] [HasSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable {𝒪 𝒪' : Sheaf J CommRingCat.{max u v}}

/- Compatibility surface for existing chapter consumers. -/
#check (restriction : (α : 𝒪 ⟶ 𝒪') →
  DerivedCategory (ringedSiteModuleCategory J 𝒪') ⥤
    DerivedCategory (ringedSiteModuleCategory J 𝒪))

end SheafOfModules.RingedSite.DerivedCoextension
