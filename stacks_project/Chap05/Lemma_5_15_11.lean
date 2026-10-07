module

public import ReasLib.Topology.Constructible.Subspace
import StacksCheckRecall

@[expose] public section

/- Lemma 5.15.11: constructible subsets restrict to constructible subspaces
of prespectral spaces. -/
@[stacks 09YI]
#check Topology.IsConstructible.preimage_subtypeVal_of_isConstructible
