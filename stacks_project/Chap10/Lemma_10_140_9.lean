/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Smooth.FractionRing
import StacksCheckRecall

/-!
# Lemma 10.140.9

@stack 07ND
-/

@[expose] public section

/- Lemma 10.140.9 [stacks 07ND]: canonical recall of the generic-point
fraction-field separability criterion. -/

@[stacks 07ND]
#check @FractionRing.isSmoothAt_bot_iff_isSeparable
