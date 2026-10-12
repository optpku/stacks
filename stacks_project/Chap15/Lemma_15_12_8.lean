/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Henselian.Pair.Product
import StacksCheckRecall

/-!
# Products of pair Henselizations

This file recalls Lemma 15.12.8 and its concrete natural comparison map from the reusable owner.

@stack 0H7Q
-/

@[expose] public section

-- The source-specified natural map `A^h → ∏ i, A_i^h`.
@[stacks 0H7Q "natural product comparison for pair Henselization"]
#check @RingPairCat.henselizationIntersectionToPi

-- Lemma 15.12.8: the map is an isomorphism for a finite nonempty pairwise-comaximal family.
@[stacks 0H7Q "Lemma 15.12.8"]
#check @RingPairCat.henselizationIntersectionToPi_bijective
