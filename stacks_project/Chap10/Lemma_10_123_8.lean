/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Algebraic.StronglyTranscendental
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.123.8 (Tag 00Q0): strong transcendence descends to a minimal-prime quotient.

@stack 00Q0
-/

-- Declarations for this item will be appended below by the statement pipeline.

-- Lemma 10.123.8: quotienting a reduced target by a minimal prime, and the base by its
-- contraction, preserves strong transcendence.
@[stacks 00Q0]
#check @IsStronglyTranscendental.quotient_over_under_of_mem_minimalPrimes
