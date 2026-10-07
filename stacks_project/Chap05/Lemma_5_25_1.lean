module

public import ReasLib.Topology.Separation.Cardinal
import StacksCheckRecall

@[expose] public section

/- Lemma 5.25.1: a dense map into a Hausdorff space gives a double-powerset cardinal bound. -/
@[stacks 0909]
#check DenseRange.cardinalMk_le_doublePowerset
