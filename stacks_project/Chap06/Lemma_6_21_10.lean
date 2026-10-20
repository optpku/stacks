module

public import ReasLib.Topology.Sheaves.Stalks.Pullback
import StacksCheckRecall

@[expose] public section

/- Lemma 6.21.10: for composable continuous maps `f : X ⟶ Y` and `g : Y ⟶ Z`, the map on
stalks induced by the composite of an `f`-map and a `g`-map is the composite of their induced
stalk maps. -/
@[stacks 008M]
#check TopCat.Sheaf.stalkMap_comp
