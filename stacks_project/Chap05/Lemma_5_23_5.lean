module

public import ReasLib.Topology.Spectral.Subspace
import StacksCheckRecall

@[expose] public section

/- Lemma 5.23.5: a constructibly closed subspace of a spectral space is
spectral. -/
@[stacks 0902]
#check IsClosed.spectralSpace_subtype_of_constructibleTopology
