module

public import ReasLib.Topology.Compactness.ClosedPoints
import StacksCheckRecall

@[expose] public section

/- Lemma 5.12.9: in a quasi-compact Kolmogorov space, the subset of closed points is compact. -/
@[stacks 08ZM]
#check @CompactSpace.isCompact_closedPoints
