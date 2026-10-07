module

public import ReasLib.Topology.ConnectedComponents.Maps
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 5.7.6

The reusable open-map bridge for maps on connected components is owned by
`ReasLib.Topology.ConnectedComponents.Maps`.
-/

/- Lemma 5.7.6: an open continuous map with connected fibers induces a bijection on connected
components. -/
@[stacks 0378]
#check @Continuous.connectedComponentsMap_bijective_of_isOpenMap_of_connectedFibers
