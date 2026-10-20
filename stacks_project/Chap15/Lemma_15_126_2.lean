/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.LocalRing.DimensionOne.MinimalPrime
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.126.2

@stack 0BWT

The minimal-prime bound is owned by the one-dimensional local-ring leaf.  Its
right-hand side is Mathlib's canonical `Ring.ord`, definitionally the length
of the corresponding principal quotient.
-/

/- Lemma 15.126.2: the number of minimal primes is bounded by the principal quotient length. -/
@[stacks 0BWT "Lemma 15.126.2, minimal-prime count bounded by principal quotient length"]
#check @IsLocalRing.DimensionOne.MinimalPrime.encard_le_ord

#check @Ring.ord
#check @Ring.ord_pow_le
