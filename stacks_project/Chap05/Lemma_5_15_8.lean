module

public import ReasLib.Topology.Constructible.Subspace
import StacksCheckRecall

@[expose] public section

/- Lemma 5.15.8: constructible subsets restrict to retrocompact subspaces of
prespectral spaces. -/
@[stacks 09YF]
#check Topology.IsConstructible.preimage_subtypeVal_of_isRetrocompact
