/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak.ExactSequence
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.66.4

@stack 0548

The reusable owners for weakly associated primes under injective maps and
exact pairs live in `ReasLib.RingTheory.Ideal.AssociatedPrime.Weak.ExactSequence`.
This file retains only the source-labelled recall surface; it does not create
a second chapter-local implementation.
-/

/- Lemma 10.66.4 (0548), clause (1): the injective-map form. -/
@[stacks 0548 "(1)"]
#check @weaklyAssociatedPrimes.subset_of_injective

/- Lemma 10.66.4 (0548), clause (2): the exact-pair form. -/
@[stacks 0548 "(2)"]
#check @weaklyAssociatedPrimes.subset_union_of_exact
