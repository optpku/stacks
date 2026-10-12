/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.LocalRing.DimensionOne.OrderOfVanishing
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.126.1

@stack 0BWS

The chapter entry recalls the exact one-dimensional local-ring statements.
The reusable power inequality and Mathlib's nonzerodivisor equality remain
available from the underlying order-of-vanishing leaf.
-/

/- Lemma 15.126.1 (1): the principal-power quotient length is bounded by its linear growth. -/
@[stacks 0BWS "Lemma 15.126.1 (1), principal-power length upper bound"]
#check @IsLocalRing.DimensionOne.principalPowerLength_le

/- Lemma 15.126.1 (2): for a nonzerodivisor, the principal-power quotient length is linear. -/
@[stacks 0BWS "Lemma 15.126.1 (2), principal-power length formula"]
#check @IsLocalRing.DimensionOne.principalPowerLength_eq_of_mem_nonZeroDivisors

#check @Ring.ord_pow_le
#check @Ring.ord_mul_le
#check @Ring.ord_pow
