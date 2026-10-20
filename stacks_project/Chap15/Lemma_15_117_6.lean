/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution.PurelyInseparableStep
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.117.6

The separable-refinement theorem is owned by `IsSolutionFor.exists_separable_of_exists`.  Keeping
the chapter entry as a recall avoids a second induction API and lets downstream users import the
ReasLib statement directly.

@stack 0BRN
-/

/- Lemma 15.117.6: a finite solution over a Nagata DVR extension admits a separable solution. -/
@[stacks 0BRN "Lemma 15.117.6: separable refinement of a solution"]
#check @IsSolutionFor.exists_separable_of_exists

#check @IsSolutionFor
#check @IsSeparableSolutionFor

end
