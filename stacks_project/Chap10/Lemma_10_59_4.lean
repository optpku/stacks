module

public import ReasLib.RingTheory.Ideal.HilbertSamuel.Comparison
import StacksCheckRecall

/-!
# Lemma 10.59.4

@stack 00K7
-/

@[expose] public section

/- Lemma 10.59.4 (Stacks 00K7): changing the ideal of definition admits a
positive reindexing comparison for Hilbert--Samuel `χ`.  The neutral owner
uses `ℕ+` for both the positive index and the reindexing factor, and also
provides the eventual `ℕ` formulation. -/
@[stacks 00K7 "positive-index form"]
#check @Ideal.HilbertSamuel.exists_reindex_chi_le

@[stacks 00K7 "eventual form"]
#check @Ideal.HilbertSamuel.exists_eventually_reindex_chi_le
