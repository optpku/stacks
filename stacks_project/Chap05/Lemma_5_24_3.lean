module

public import ReasLib.Topology.Spectral.Limit.Eventual
import StacksCheckRecall

@[expose] public section

/-
Lemma 5.24.3 is the eventual-stage inclusion criterion for constructibly closed and
constructibly open subsets in a cofiltered spectral inverse system.
-/

@[stacks 0A2X]
#check limit_projection_preimage_subset_iff_exists_stage_preimage_subset
