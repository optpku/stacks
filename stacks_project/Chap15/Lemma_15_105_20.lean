/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Localization.FractionRing.WeakDimensionPullback
import StacksCheckRecall

@[expose] public section

/-!
# A cartesian square over a fraction field

Lemma 15.105.20 is owned by the reusable fraction-ring pullback theorem.

@stack 092U
-/

/- Lemma 15.105.20: a normal domain and its fraction field admit the specified
weak-dimension-one cartesian presentation. -/
@[stacks 092U "Lemma 15.105.20"]
#check @FractionRing.exists_pullback_with_weakDimensionLE_one
