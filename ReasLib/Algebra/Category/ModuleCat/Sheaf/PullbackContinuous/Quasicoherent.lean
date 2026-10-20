/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback of Quasi-coherent Sheaves of Modules

The canonical inverse-image functor associated to a continuous final functor preserves
quasi-coherence over arbitrary sheaves of rings. Commutativity and pullbacks in the sites are not
part of this property-preservation interface.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u₁ v₁ u₂ v₂ w

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable {F : D ⥤ C} [F.IsContinuous K J]
variable {R : Sheaf J RingCat.{w}} {S : Sheaf K RingCat.{w}}
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : D, HasWeakSheafify (K.over U) AddCommGrpCat.{w}]
variable [∀ U : D, (K.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (f : S ⟶ (F.sheafPushforwardContinuous RingCat.{w} K J).obj R)
variable [(SheafOfModules.pushforward f).IsRightAdjoint]

/-- Inverse image preserves quasi-coherent sheaves of modules. -/
@[stacks 03DO "(6)", stacks 01BG]
instance pullback_isQuasicoherent
    [F.Final] (M : SheafOfModules.{w} S) [M.IsQuasicoherent] :
    ((SheafOfModules.pullback f).obj M).IsQuasicoherent := sorry

end SheafOfModules
