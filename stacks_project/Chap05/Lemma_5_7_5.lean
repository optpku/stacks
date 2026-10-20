module

public import ReasLib.Topology.ConnectedComponents.Maps
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 5.7.5

The reusable closed-set quotient bridge for maps on connected components is owned by
`ReasLib.Topology.ConnectedComponents.Maps`.
-/

/- Lemma 5.7.5: connected fibers and the closed-set quotient condition induce a bijection on
connected components. -/
@[stacks 0377]
#check @connectedComponentsMap_bijective_of_isClosed_iff_preimage
