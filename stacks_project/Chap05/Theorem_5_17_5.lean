module

public import ReasLib.Topology.Maps.Proper.Characterization
import StacksCheckRecall

@[expose] public section

/- Theorem 5.17.5: the four standard continuous proper-map formulations are
equivalent. -/
@[stacks 005R]
#check @Continuous.isProperMap_tfae
