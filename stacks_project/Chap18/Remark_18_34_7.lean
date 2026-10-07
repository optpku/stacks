module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.PrincipalParts.BaseChange.System
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.PrincipalParts.FirstOrder.BaseChange
import StacksCheckRecall

@[expose] public section

/-! Remark 18.34.7 (0G3W): a commutative square of structure-sheaf maps and a compatible
module morphism induce a morphism of the inverse systems of principal-parts sheaves.  The maps
compose, commute with order truncation, and preserve the canonical first-order sequence. -/
@[stacks 0G3W]
#check @SheafOfModules.RingedSite.PrincipalParts.BaseChange.systemMap

#check @SheafOfModules.RingedSite.PrincipalParts.BaseChange.systemMap_naturality

#check @SheafOfModules.RingedSite.PrincipalParts.BaseChange.systemMap_comp

#check @SheafOfModules.RingedSite.PrincipalParts.FirstOrder.BaseChange.sequenceMap
