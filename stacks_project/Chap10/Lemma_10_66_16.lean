/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak.Localization
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.66.16
@stack 05CA

The source-facing equality is owned by the canonical weak-associated-prime
localization namespace; this chapter file records the textbook recall.
-/

@[stacks 05CA "Lemma 10.66.16"]
#check @weaklyAssociatedPrimes.Localization.eq_of_isSMulRegular
