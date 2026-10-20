/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous.LocallyFree

/-!
# Pullback of Locally Free Sheaves of Modules

Local freeness and finite local freeness are preserved by the canonical inverse-image functor
attached to a continuous final functor and a morphism of ring sheaves. Neither property requires
commutativity of the rings.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u₁ v₁ u₂ v₂ w

namespace SheafOfModules.RingedSite

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

/-- The inverse image along a continuous final functor preserves locally free sheaves of modules. -/
abbrev pullback_isLocallyFree
    [F.Final] (M : SheafOfModules.{w} S) [M.IsLocallyFree] :
    ((SheafOfModules.pullback f).obj M).IsLocallyFree :=
  SheafOfModules.pullback_isLocallyFree f M

/-- The inverse image along a continuous final functor preserves finite locally free sheaves of modules. -/
abbrev pullback_isFiniteLocallyFree
    [F.Final] (M : SheafOfModules.{w} S) [IsFiniteLocallyFree M] :
    IsFiniteLocallyFree ((SheafOfModules.pullback f).obj M) :=
  SheafOfModules.pullback_isFiniteLocallyFree f M

end SheafOfModules.RingedSite
