module

public import ReasLib.Topology.Jacobson.Basic
import StacksCheckRecall

@[expose] public section

/- Lemma 5.18.3: a non-Jacobson Kolmogorov prespectral space has a non-closed
point whose singleton is locally closed. -/
@[stacks 02I7]
#check PrespectralSpace.exists_nonclosedPoint_with_locallyClosedSingleton
