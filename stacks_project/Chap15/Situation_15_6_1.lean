/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Pullback.Surjective
import StacksCheckRecall

/-!
# Situation 15.6.1

@stack 08KH
-/

@[expose] public section

/- Situation 15.6.1, tag `08KH`: a surjective ring pullback situation and its canonical
fiber-product ring. -/
@[stacks 08KH "situation"]
#check @SurjectiveRingPullbackSituation

@[stacks 08KH "fiber product"]
#check @SurjectiveRingPullbackSituation.Bprime

@[stacks 08KH "first projection"]
#check @SurjectiveRingPullbackSituation.bprimeToB

@[stacks 08KH "second projection"]
#check @SurjectiveRingPullbackSituation.bprimeToAprime

@[stacks 08KH "commutativity"]
#check @SurjectiveRingPullbackSituation.comm

@[stacks 08KH "pullback square"]
#check @SurjectiveRingPullbackSituation.isPullback
