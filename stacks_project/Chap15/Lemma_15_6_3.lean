/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Pullback.Integral
import StacksCheckRecall

@[expose] public section

/-!
@stack 0E1S

Lemma 15.6.3 is the canonical integrality theorem for the projection from a surjective ring
pullback.  The reusable statement is owned by `SurjectiveRingPullbackSituation`.
-/

/- Lemma 15.6.3 (0E1S): if `B ⟶ A` is integral in a surjective ring-pullback situation, then
the canonical projection `B' ⟶ A'` is integral. -/
@[stacks 0E1S "integrality of the surjective pullback projection"]
#check @SurjectiveRingPullbackSituation.bprimeToAprime_isIntegral
