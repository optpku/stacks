/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Extension.Infinitesimal

/-!
# Mixed-scalar extensions on a first-order thickening

This module exposes the shared mixed-scalar extension API to source-facing consumers.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.FirstOrderThickening

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {𝒪' 𝒪 : Sheaf J CommRingCat.{max u v}} {π : 𝒪' ⟶ 𝒪}

#check (shortComplex : (E : Extension π) →
  ShortComplex (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪'))

end SheafOfModules.RingedSite.FirstOrderThickening
