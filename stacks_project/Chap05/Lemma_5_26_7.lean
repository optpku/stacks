module

public import ReasLib.Topology.Maps.Surjective
import StacksCheckRecall

@[expose] public section

/- Lemma 5.26.7: a nonidentity continuous surjective self-map has a proper closed image cover. -/
@[stacks 090B]
#check Continuous.exists_proper_closed_cover_of_surjective_ne_id
