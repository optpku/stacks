module

public import ReasLib.Topology.Constructible.Local
import StacksCheckRecall

@[expose] public section

/- Lemma 5.15.14: constructibility is local on a finite constructible cover. -/
@[stacks 09YK]
#check Topology.IsConstructible.iff_of_finiteCover
