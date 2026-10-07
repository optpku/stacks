module

public import ReasLib.Topology.Constructible.Subspace
import StacksCheckRecall

@[expose] public section

/- Lemma 5.15.4: a constructible subset has constructible trace on an open
subspace. -/
@[stacks 005J "constructible traces on open subspaces"]
#check Topology.IsConstructible.preimage_subtypeVal_of_isOpen
