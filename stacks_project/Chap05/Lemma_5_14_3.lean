module

public import ReasLib.Topology.Category.TopCat.Limits.Recognition
import StacksCheckRecall

@[expose] public section

/- Lemma 5.14.3: a cone of topological spaces is limiting when its underlying
cone of types is limiting and projection preimages form a basis. -/
@[stacks 0A2Q]
#check TopCat.Cone.isLimit_of_forgetIsLimit_of_preimageBasis
