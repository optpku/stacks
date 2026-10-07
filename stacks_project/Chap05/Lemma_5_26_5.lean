module

public import Mathlib.Topology.ExtremallyDisconnected
import StacksCheckRecall

@[expose] public section

/- Lemma 5.26.5 is exactly Mathlib's compact minimal-surjection construction. -/
@[stacks 08YM]
#check exists_compact_surjective_zorn_subset
