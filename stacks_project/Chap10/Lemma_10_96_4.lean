/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.Exactness.ShortComplex.Power
import StacksCheckRecall

@[expose] public section

/-!
# Completion of a short exact sequence with power-annihilated cokernel

@stack 0BNG
-/

/- Lemma 10.96.4: a power-annihilated target is complete for the adic topology. -/
@[stacks 0BNG "power-annihilated target completeness"]
#check @IsAdicComplete.of_pow_smul_top_eq_bot

/- Lemma 10.96.4: the canonical map from the completed middle term to the target. -/
@[stacks 0BNG "canonical target map"]
#check @AdicCompletion.mapToPowSmulTopEqBot

/- Lemma 10.96.4: completion gives the asserted short exact sequence. -/
@[stacks 0BNG "short exact sequence"]
#check @AdicCompletion.completion_shortExact_of_pow_smul_top_eq_bot
