module

public import ReasLib.Topology.ConstructibleTopology.Maps
import StacksCheckRecall

@[expose] public section

/- Lemma 5.23.3 (1): a spectral map is continuous for constructible
topologies. -/
@[stacks 0A2S "constructible-topology continuity"]
#check IsSpectralMap.continuous_constructibleTopology

/- Lemma 5.23.3 (2): fibers of a spectral map of spectral spaces are compact. -/
@[stacks 0A2S "compact fibers"]
#check IsSpectralMap.isCompact_fiber

/- Lemma 5.23.3 (3): the range of a spectral map of spectral spaces is
constructibly closed. -/
@[stacks 0A2S "constructibly closed range"]
#check IsSpectralMap.isClosed_range_constructibleTopology
