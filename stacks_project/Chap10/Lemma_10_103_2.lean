/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.CohenMacaulay.Module.RegularSequence.GoodElement
import StacksCheckRecall

/-!
# Good elements for Cohen--Macaulay modules

The source condition is phrased through the equivalent prefix-quotient
description of the relevant support intersections.

@stack 00N4
-/

/- Lemma 10.103.2 (1): a good element is regular. -/
@[stacks 00N4 "(1)"]
#check @Module.IsGoodWithRespectTo.isSMulRegular

/- Lemma 10.103.2 (2): the quotient remains Cohen--Macaulay. -/
@[stacks 00N4 "(2)"]
#check @Module.IsGoodWithRespectTo.cohenMacaulay_quotSMulTop

/- Lemma 10.103.2 (3): the shortened sequence remains maximal regular. -/
@[stacks 00N4 "(3)"]
#check @Module.IsGoodWithRespectTo.isRegular_take_and_supportDim_quotSMulTop_eq

@[stacks 00N4 "good element predicate"]
#check @Module.IsGoodWithRespectTo
