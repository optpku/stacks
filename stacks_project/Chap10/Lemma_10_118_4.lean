module

public import ReasLib.RingTheory.GenericFlatness.Locus.ShortExact
import StacksCheckRecall

@[expose] public section

/-!
# Generic-Flatness Loci in Short Exact Sequences

The source inclusion is recalled from the canonical generic-flatness locus API.

@stack 051W
-/

/- Lemma 10.118.4: for a short exact sequence `0 → M₁ → M₂ → M₃ → 0`
of `S`-modules, the intersection of the good loci of the outer terms is
contained in the good locus of the middle term. -/
@[stacks 051W]
#check @GenericFlatness.ShortExact.goodLocus_inter_subset
