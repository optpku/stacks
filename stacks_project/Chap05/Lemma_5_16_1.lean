module

public import ReasLib.Topology.Noetherian.Constructible
import StacksCheckRecall

@[expose] public section

/- Lemma 5.16.1: in a Noetherian topological space, constructible subsets are
exactly finite unions of locally closed subsets. -/
@[stacks 005L]
#check @Topology.isConstructible_iff_isFiniteUnionOfLocallyClosed_of_noetherian
