/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
import StacksCheckRecall

/-!
# Lemma 18.12.4

The tensor-pullback/direct-image correspondence is the Hom equivalence of the canonical
pullback-pushforward adjunction, specialized to the direct-image ring sheaf.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
variable (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
variable (F : D ⥤ C) [Functor.IsContinuous F JD JC]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable (𝒪 : Sheaf JC RingCat.{u})
variable (𝒢 : SheafOfModules ((F.sheafPushforwardContinuous RingCat.{u} JD JC).obj 𝒪))
variable (ℱ : SheafOfModules 𝒪)

/- Lemma 18.12.4 (03D4): tensor pullback from the direct-image ring and direct image form
the canonical adjunction on module sheaves. -/
@[stacks 03D4]
#check
  (((SheafOfModules.pullbackPushforwardAdjunction
      (𝟙 ((F.sheafPushforwardContinuous RingCat.{u} JD JC).obj 𝒪))).homEquiv 𝒢 ℱ) :
    ((SheafOfModules.pullback
        (𝟙 ((F.sheafPushforwardContinuous RingCat.{u} JD JC).obj 𝒪))).obj 𝒢 ⟶ ℱ) ≃
      (𝒢 ⟶ (SheafOfModules.pushforward
        (𝟙 ((F.sheafPushforwardContinuous RingCat.{u} JD JC).obj 𝒪))).obj ℱ))
