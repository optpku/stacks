/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.66.5

@stack 0588

The reusable owner states the source equivalence with its sides in the
canonical set-first order. Symmetry of `Iff` gives the source's module-first
wording without a chapter-level alias.
-/

@[stacks 0588 "weakly associated primes of a subsingleton module"]
#check @weaklyAssociatedPrimes.eq_empty_of_subsingleton

@[stacks 0588 "existence of a weakly associated prime"]
#check @weaklyAssociatedPrimes.nonempty

@[stacks 0588 "canonical empty-set criterion"]
#check @weaklyAssociatedPrimes.eq_empty_iff_subsingleton
