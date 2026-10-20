/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.FlatQuotient.ClosedFiber
import StacksCheckRecall

/-!
# Noetherian local base-change criterion

Lemma 15.20.2 identifies closed-fiber flatness after a Noetherian local base change with
vanishing of the least closed-fiber flat quotient ideal.

@stack 0527
-/

@[stacks 0527 "Lemma 15.20.2"]
#check @Ideal.IsClosedFiberFlatQuotient.baseChange_iff_map_eq_bot_of_noetherian

@[stacks 0527 "closed-fiber flat quotient ideal"]
#check @Ideal.IsClosedFiberFlatQuotient
