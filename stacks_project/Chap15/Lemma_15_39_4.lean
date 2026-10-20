/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Completion.Pullback
import StacksCheckRecall

/-!
# Lemma 15.39.4

@stack 09Q8
-/

@[expose] public section

/- Lemma 15.39.4 (1), tag `09Q8`: the fiber product of two complete Noetherian local rings over
a common quotient is complete local. -/
@[stacks 09Q8 "part 1"]
#check @SurjectiveRingPullbackSituation.bprime_isCompleteLocalRing_of_surjective

/- Lemma 15.39.4 (2), tag `09Q8`: the same fiber-product ring is Noetherian. -/
@[stacks 09Q8 "part 2"]
#check @SurjectiveRingPullbackSituation.bprime_isNoetherianRing_of_surjective
