/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak.ZeroDivisor
import StacksCheckRecall

/-!
# Weakly associated primes and zero divisors

@stack 05C3
-/

@[expose] public section

/- Lemma 10.66.7: the union of the weakly associated primes of an `R`-module is
the set of zero divisors on that module. -/
@[stacks 05C3]
#check @weaklyAssociatedPrimes.biUnion_eq_zero_divisors
