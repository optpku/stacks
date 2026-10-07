module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.PrincipalParts.BaseChange.System
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.PrincipalParts.FirstOrder.BaseChange
import StacksCheckRecall

@[expose] public section

/- Remark 17.29.7 (0G3W): a commutative square of ring sheaves and a compatible module map
induce a morphism of the inverse systems of principal-parts sheaves. These morphisms compose and
are compatible, in order one, with the canonical first principal-parts sequence. -/
@[stacks 0G3W]
#check @SheafOfModules.RingedSite.PrincipalParts.BaseChange.systemMap

#check @SheafOfModules.RingedSite.PrincipalParts.BaseChange.systemMap_comp

#check @SheafOfModules.RingedSite.PrincipalParts.FirstOrder.BaseChange.Presentation.sequenceMap

#check @SheafOfModules.RingedSite.PrincipalParts.FirstOrder.BaseChange.sequenceMap

#check @SheafOfModules.RingedSite.PrincipalParts.FirstOrder.BaseChange.sequenceIso_naturality

#check @SheafOfModules.RingedSite.PrincipalParts.FirstOrder.BaseChange.sequenceMap_comp
