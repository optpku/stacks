module

public import ReasLib.Topology.Sheaf.BaseChange.Proper
import StacksCheckRecall

@[expose] public section

/- [stacks 0D90] Lemma 20.18.3 (Proper base change for sheaves of sets): the canonical
set-valued sheaf base-change map is an isomorphism for a proper cartesian square. The source's
properness requires both `IsProperMap` and `IsSeparatedMap`. -/

namespace TopCat.Sheaf.BaseChange

#check @pullbackIso
#check @map
@[stacks 0D90] #check @map_app_isIso_of_proper
#check @map_isIso_of_proper

end TopCat.Sheaf.BaseChange
