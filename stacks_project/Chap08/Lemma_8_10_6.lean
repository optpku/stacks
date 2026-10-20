module

public import ReasLib.CategoryTheory.Fibered.Stack.InheritedTopology.Composition
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

/- Lemma 8.10.6 (1): stack conditions compose across the topology inherited by an intermediate
projection. -/
@[stacks 09WX "(1) stack composition"]
#check @IsStack.OnSite.comp_of_inheritedTopology

/- Lemma 8.10.6 (2): the groupoid-valued version composes as well. -/
@[stacks 09WX "(2) groupoid composition"]
#check @IsStack.InGroupoids.comp_of_inheritedTopology
#check @IsStack.InSetoids.comp_of_inheritedTopology
#check @IsStack.InSets.comp_of_inheritedTopology

/- The converse groupoid criterion is also reusable when the intermediate projection is known to
be fibered in groupoids. -/
#check @IsStack.InGroupoids.of_comp_inheritedTopology

end CategoryTheory
