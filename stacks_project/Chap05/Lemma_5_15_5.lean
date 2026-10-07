module

public import ReasLib.Topology.Constructible.Subspace
import StacksCheckRecall

@[expose] public section

/- Lemma 5.15.5: constructible subsets of retrocompact open subspaces are
constructible in the ambient space. -/
@[stacks 09YD]
#check Topology.IsConstructible.image_subtypeVal_of_isRetrocompact
