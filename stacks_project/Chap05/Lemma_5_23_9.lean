module

public import ReasLib.Topology.ConnectedComponents.Profinite
import StacksCheckRecall

@[expose] public section

/- Lemma 5.23.9: connected components of a spectral space form a profinite
space. -/
@[stacks 0906]
#check ConnectedComponents.exists_profinite_of_spectralSpace
