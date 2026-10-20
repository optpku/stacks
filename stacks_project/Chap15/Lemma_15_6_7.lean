/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.PullbackAdjunction.Finite
import StacksCheckRecall

/-!
# Lemma 15.6.7

The source statement is the finiteness theorem for the shared fibre-product right adjoint.

@stack 0D2H
-/

@[expose] public section

open CategoryTheory

universe u


variable {B A A' : Type u} [CommRing B] [CommRing A] [CommRing A']
variable (S : SurjectiveRingPullbackSituation B A A')

/- Lemma 15.6.7: a pullback-module triple finite on both components has a finite fibre-product
module over the pullback ring. -/
@[stacks 0D2H "finite fibre-product module"]
#check (ModuleCat.Pullback.rightAdjoint_finite S)
