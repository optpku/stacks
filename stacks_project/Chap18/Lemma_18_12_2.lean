/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Sites.Pullback
import StacksCheckRecall

/-!
# Lemma 18.12.2

Inverse image of module sheaves is the canonical `SheafOfModules.pullback`, specialized to the
unit map into the direct image of the inverse-image ring sheaf.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
variable (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
variable (F : D ⥤ C) [Functor.IsContinuous F JD JC]
variable [HasWeakSheafify JC RingCat.{u}]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf JD RingCat.{u})

/- Lemma 18.12.2 (03D2): inverse image gives a functor from `𝒪`-modules to modules over
the inverse-image ring sheaf. -/
@[stacks 03D2]
#check
  (SheafOfModules.pullback
      ((F.sheafAdjunctionContinuous RingCat.{u} JD JC).unit.app 𝒪) :
    SheafOfModules 𝒪 ⥤
      SheafOfModules ((F.sheafPullback RingCat.{u} JD JC).obj 𝒪))
