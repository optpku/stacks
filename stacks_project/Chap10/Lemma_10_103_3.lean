/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.CohenMacaulay.Module.Quotient
import StacksCheckRecall

/-!
# A one-step support-dimension drop

The source intersection `Module.support R M ∩ PrimeSpectrum.zeroLocus {g}`
is represented by the canonically equal support of `QuotSMulTop g M`.

@stack 00N5
-/

/- The support of the principal quotient is the source's intersection with
the singleton zero locus. -/
@[stacks 00N5 "support view"]
#check @Module.support_quotSMulTop

/- Lemma 10.103.3 (1): a one-step support-dimension drop makes the parameter
regular on a Cohen--Macaulay module. -/
@[stacks 00N5 "(1)"]
#check @Module.CohenMacaulay.QuotSMulTop.isSMulRegular_of_dim_drop

/- Lemma 10.103.3 (2): the quotient remains Cohen--Macaulay. -/
@[stacks 00N5 "(2)"]
#check @Module.CohenMacaulay.QuotSMulTop.cohenMacaulay_of_dim_drop

/- Lemma 10.103.3 (3): quotient depth drops by one. -/
@[stacks 00N5 "(3)"]
#check @Module.CohenMacaulay.QuotSMulTop.moduleDepth_eq_sub_one_of_dim_drop
