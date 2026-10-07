module

public import ReasLib.Topology.Spectral.Limit.CompactOpens
import StacksCheckRecall

@[expose] public section

/-
Lemma 5.24.6 recalls descent and eventual-refinement results for compact open subsets of
cofiltered spectral inverse limits.
-/

/- Lemma 5.24.6 (1): compact opens of the limit descend from one stage. -/
@[stacks 0A30 "quasi-compact opens descend from a stage"]
#check compact_open_eq_preimage_of_limit

/- Lemma 5.24.6 (2): inclusion of compact-open pullbacks descends to a common refinement. -/
@[stacks 0A30 "inclusions of pulled-back quasi-compact opens descend to a common stage"]
#check exists_common_refinement_of_preimage_subset

/- Lemma 5.24.6 (3): finite-union identities descend to one stage. -/
@[stacks 0A30 "finite union identities of pulled-back quasi-compact opens descend"]
#check exists_stage_of_preimage_eq_iUnion

/- Lemma 5.24.6 (4): finite-intersection identities descend to one stage. -/
@[stacks 0A30 "finite intersection identities of pulled-back quasi-compact opens descend"]
#check exists_stage_of_preimage_eq_iInter
