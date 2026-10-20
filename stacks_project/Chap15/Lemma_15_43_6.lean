/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.AnalyticallyUnramified.ReducedCompletion
import StacksCheckRecall

/-!
# Lemma 15.43.6

@stack 07NZ
-/

@[expose] public section

/- Lemma 15.43.6 (1): reducedness descends from the maximal-ideal adic completion. -/
@[stacks 07NZ "Lemma 15.43.6 (1)"]
#check @IsAnalyticallyUnramified.isReduced_of_completion

/- Lemma 15.43.6 (2): a reduced Noetherian local ring can have nonreduced completion. -/
@[stacks 07NZ "Lemma 15.43.6 (2)"]
#check @IsAnalyticallyUnramified.exists_reduced_with_nonreduced_completion

/- Lemma 15.43.6 (3): reducedness is detected by completion for local Nagata rings. -/
@[stacks 07NZ "Lemma 15.43.6 (3)"]
#check @NagataRing.isReduced_iff_completion_isReduced
