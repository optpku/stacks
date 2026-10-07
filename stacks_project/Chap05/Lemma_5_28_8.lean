module

public import ReasLib.Topology.Stratification.Refinement
import StacksCheckRecall

@[expose] public section

/- Lemma 5.28.8: finite partitions of Noetherian spaces admit finite good locally closed
refinements. -/
@[stacks 09Y5]
#check Setoid.Partitions.exists_finite_good_refinement
