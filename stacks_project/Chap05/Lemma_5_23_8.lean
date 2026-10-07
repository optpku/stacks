module

public import ReasLib.Topology.ConstructibleTopology.Profinite
import StacksCheckRecall

@[expose] public section

/- Lemma 5.23.8: the standard separation, specialization, and patch-topology
criteria for a spectral space to be profinite are equivalent. -/
@[stacks 0905]
#check SpectralSpace.profinite_criteria
