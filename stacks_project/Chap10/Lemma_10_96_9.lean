module

public import ReasLib.RingTheory.AdicCompletion.Cofinal
import StacksCheckRecall

/-!
# Completion for cofinal ideal-power filtrations

This file records Lemma 10.96.9.  The reusable comparison maps and completion
equivalence are owned by `ReasLib.RingTheory.AdicCompletion.Cofinal`.

@stack 0319
-/

@[expose] public section

@[stacks 0319 "canonical comparison map"]
#check @AdicCompletion.comparisonMapOfPowLe

@[stacks 0319 "completion equivalence"]
#check @AdicCompletion.linearEquivOfPowLe

@[stacks 0319 "adic-completeness comparison"]
#check @AdicCompletion.isAdicComplete_iff_of_pow_le
