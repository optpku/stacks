/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite

/-!
# Sheafification of modules on a ringed site

This leaf owns the canonical sheafification functor for module presheaves over a
fixed commutative ring sheaf.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite (ringSheaf ringedSiteModuleCategory)

noncomputable section

universe u v w z

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{z}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{z}]

/-- Sheafification of presheaves of modules over a fixed commutative ring sheaf. -/
noncomputable abbrev moduleSheafification (𝒪 : Sheaf J CommRingCat.{w}) :
    PresheafOfModules.{z} (ringSheaf J 𝒪).obj ⥤
      ringedSiteModuleCategory.{u, v, z, w} J 𝒪 :=
  PresheafOfModules.sheafification.{z} (𝟙 (ringSheaf J 𝒪).obj)
