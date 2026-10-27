/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Crystal

@[expose] public section

open CategoryTheory SheafOfModules

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{w}}
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

#check (SheafOfModules.isCrystalInQuasiCoherentModules_iff : ∀ (F : SheafOfModules.{w} R),
    IsCrystalInQuasiCoherentModules F ↔ F.IsQuasicoherent)

#check (SheafOfModules.IsCrystalInFiniteLocallyFreeModules.spec : ∀ (F : SheafOfModules.{w} R),
    IsCrystalInFiniteLocallyFreeModules F ↔
      F.IsQuasicoherent ∧ F.IsFiniteLocallyFree)

