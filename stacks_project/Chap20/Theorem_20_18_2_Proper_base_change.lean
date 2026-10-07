module

public import ReasLib.Topology.Sheaf.Derived.BaseChange.Proper
import StacksCheckRecall

@[expose] public section

/- [stacks 09V6] Theorem 20.18.2 (Proper base change): for a cartesian square of topological
spaces with proper vertical map, every bounded-below abelian-sheaf base-change component is an
isomorphism. -/

namespace TopCat.Sheaf.BoundedBaseChange

#check @source
#check @target
#check @sourceComparison
#check @targetComparison
#check @mapOfIso
#check @appOfIso
#check @IsMapOfIso
#check @IsMap
#check @IsMapAt
#check @mapOfIso_isMapOfIso
#check @mapOfIso_isMap
#check @mapOfIso_isMapAt
@[stacks 09V6] #check @IsMapAt.isIso_of_proper
#check @IsMap.isIso_of_proper
#check @appOfIso_isIso_of_proper
#check @mapOfIso_isIso_of_proper

end TopCat.Sheaf.BoundedBaseChange
