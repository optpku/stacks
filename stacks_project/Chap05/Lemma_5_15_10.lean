module

public import ReasLib.Topology.Constructible.Retrocompact
import StacksCheckRecall

@[expose] public section

/- Lemma 5.15.10: every constructible subset is retrocompact. -/
@[stacks 09YH]
#check Topology.IsConstructible.isRetrocompact
