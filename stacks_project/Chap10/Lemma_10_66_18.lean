/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak.BaseChange.Textbook
import StacksCheckRecall

@[expose] public section

/-!
# Weakly associated primes after fraction-field base change

@stack 05CC

The source-facing tensor statement is owned by the textbook base-change leaf;
this chapter file records the canonical recall.
-/

@[stacks 05CC "Lemma 10.66.18"]
#check @weaklyAssociatedPrimes.BaseChange.Textbook.eq_image_comap_fractionRingBaseChange
