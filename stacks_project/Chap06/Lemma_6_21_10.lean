/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaves.Stalks.Pullback
import StacksCheckRecall

@[expose] public section

/- Lemma 6.21.10: for composable continuous maps `f : X ⟶ Y` and `g : Y ⟶ Z`, the map on
stalks induced by the composite of an `f`-map and a `g`-map is the composite of their induced
stalk maps. -/
@[stacks 008M]
#check TopCat.Sheaf.stalkMap_comp
