/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak.Restriction
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.66.11

@stack 05C6

The restriction-of-scalars inclusion is owned directly by ReasLib.
-/

/- Lemma 10.66.11: weakly associated primes after restricting scalars lie
in the contraction image of the weakly associated primes over the larger
ring. -/
@[stacks 05C6]
#check @weaklyAssociatedPrimes.Restriction.subset_comap_image
