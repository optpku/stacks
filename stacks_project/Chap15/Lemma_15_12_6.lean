/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Henselian.Pair.Radical
import StacksCheckRecall

/-!
# Pair Henselization depends only on the zero locus

This file recalls Lemma 15.12.6 from the reusable pair-Henselization API.

@stack 0F0L
-/

@[expose] public section

-- Lemma 15.12.6: `V(I) = V(J)` gives a unique compatible equivalence `A_I^h ≃ₐ[A] A_J^h`.
@[stacks 0F0L "Lemma 15.12.6"]
#check @RingPairCat.henselizationRing_existsUnique_algEquiv_of_zeroLocus_eq
