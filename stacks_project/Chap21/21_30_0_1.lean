module

public import ReasLib.CategoryTheory.Sites.TopologyComparison.Sheaf
public import ReasLib.CategoryTheory.Sites.Over.Adjunction
import StacksCheckRecall

@[expose] public section

/-!
# Equation 21.30.0.1

The compatibility square of the two localized topology-comparison morphisms is owned by
`GrothendieckTopology.overMapComparison`.  The inverse-image mate and the cocontinuous
direct-image presentation are separate reusable views of the same square.
-/

open CategoryTheory

/- Equation 21.30.0.1 (0EZ2): topology comparison commutes with relocalization. -/
@[stacks 0EZ2 "topology-comparison/relocalization square"]
#check @GrothendieckTopology.overMapComparison

/- The inverse-image mate of the source square. -/
@[stacks 0EZ2 "inverse-image mate of the topology-comparison square"]
#check @GrothendieckTopology.overMapPullbackComparisonIso

/- The canonical continuous direct-image functor on an over-site. -/
#check @GrothendieckTopology.overMapPushforward

/- The cocontinuous presentation of that direct image. -/
#check @GrothendieckTopology.overMapPushforwardIsoCocontinuous

/- The adjunction used to pass between the direct- and inverse-image views. -/
#check @GrothendieckTopology.overMapPushforwardAdjunction

end
