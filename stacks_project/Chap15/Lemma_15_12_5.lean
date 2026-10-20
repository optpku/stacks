module

public import ReasLib.RingTheory.Henselian.Pair.FilteredColimit
import StacksCheckRecall

/-!
# Filtered colimits of pair Henselizations

This file recalls the categorical form of Lemma 15.12.5 from the reusable owner.

@stack 0A04
-/

@[expose] public section

-- Lemma 15.12.5: `(A, I) ↦ (A^h, I^h)` preserves filtered colimits.
@[stacks 0A04 "Lemma 15.12.5"]
#check @RingPairCat.pairHenselization_preservesFilteredColimits
