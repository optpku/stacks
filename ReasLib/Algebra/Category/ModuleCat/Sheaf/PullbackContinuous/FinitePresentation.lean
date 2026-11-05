/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback of Finitely Presented Sheaves of Modules

The canonical inverse-image functor associated to a continuous representably flat functor
preserves Mathlib's finite-presentation predicate over arbitrary sheaves of rings.
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

/-- Lemma 18.23.4 (7) (03DO): inverse image along a continuous representably flat functor
preserves finitely presented sheaves of modules. -/
@[stacks 03DO "(7)", stacks 01BQ]
instance pullback_isFinitePresentation
    [RepresentablyFlat F] (M : SheafOfModules.{w} S) [M.IsFinitePresentation] :
    ((SheafOfModules.pullback f).obj M).IsFinitePresentation := sorry

end SheafOfModules
