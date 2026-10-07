module

public import ReasLib.Topology.Constructible.Subspace
import StacksCheckRecall

@[expose] public section

/- Lemma 5.15.12: constructible subsets of constructible subspaces have
constructible ambient image. -/
@[stacks 09YJ]
#check Topology.IsConstructible.image_subtypeVal_of_isConstructible
