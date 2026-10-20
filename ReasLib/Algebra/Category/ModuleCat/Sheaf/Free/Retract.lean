/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Retract
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Basic

/-!
# Retracts of finite free sheaves of modules

This leaf owns the object property of being a retract of a finite free sheaf.  It is separated
from complexes and perfectness so that module-level arguments can use it directly.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace SheafOfModules

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]

/-- The object property of `𝒪`-modules that are retracts of finite free modules. -/
abbrev finiteFreeRetractModuleProperty
    (𝒪 : Sheaf J RingCat.{w}) : ObjectProperty (SheafOfModules.{w} 𝒪) :=
  ObjectProperty.retractClosure
    (fun M : SheafOfModules.{w} 𝒪 ↦ _root_.SheafOfModules.IsFiniteFree M)

end

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]

/-- Every finite free module belongs to the finite-free retract closure. -/
theorem finiteFreeRetractModuleProperty_of_isFiniteFree
    {𝒪 : Sheaf J RingCat.{w}} (M : SheafOfModules.{w} 𝒪) [IsFiniteFree M] :
    finiteFreeRetractModuleProperty 𝒪 M := sorry

/-- A module belongs to `finiteFreeRetractModuleProperty` exactly when it is a direct retract
of a finite free module. -/
theorem finiteFreeRetractModuleProperty_iff
    {𝒪 : Sheaf J RingCat.{w}} (M : SheafOfModules.{w} 𝒪) :
    finiteFreeRetractModuleProperty 𝒪 M ↔
      ∃ I : Type w, Finite I ∧
        Nonempty (Retract M (_root_.SheafOfModules.free I : SheafOfModules.{w} 𝒪)) := sorry

/-- A direct retract of a finite free module satisfies `finiteFreeRetractModuleProperty`. -/
theorem finiteFreeRetractModuleProperty_of_retract_free
    {𝒪 : Sheaf J RingCat.{w}} {M : SheafOfModules.{w} 𝒪} {I : Type w}
    [Finite I] (r : Retract M (_root_.SheafOfModules.free I : SheafOfModules.{w} 𝒪)) :
    finiteFreeRetractModuleProperty 𝒪 M := sorry

end

end SheafOfModules
