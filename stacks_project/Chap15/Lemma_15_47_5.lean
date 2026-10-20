/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Regular.JRing.FiniteTypeDomain
import StacksCheckRecall

/-!
# Lemma 15.47.5

@stack 07PB
-/

@[expose] public section

/-! # Lemma 15.47.5: separable generic ascent of J-0 -/

/- Lemma 15.47.5, tag `07PB`: `J-0` ascends when the induced fraction-field extension is
separable. -/
@[stacks 07PB "separable generic ascent of J-0"]
#check @IsJ0Ring.FiniteTypeDomain.ascend
