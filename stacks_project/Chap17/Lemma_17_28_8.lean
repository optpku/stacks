module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Differentials.BaseChange
import StacksCheckRecall

@[expose] public section

/-! Lemma 17.28.8 (08RS): a commutative square of sheaves of commutative rings induces the
canonical map on relative differentials, characterized by `d f ↦ d (b f)` and functorial under
composition of squares. -/
@[stacks 08RS]
#check @SheafOfModules.RingedSite.RelativeDifferentials.map

#check @SheafOfModules.RingedSite.RelativeDifferentials.map_d

#check @SheafOfModules.RingedSite.RelativeDifferentials.map_unique

#check @SheafOfModules.RingedSite.RelativeDifferentials.map_comp
#check @SheafOfModules.RingedSite.RelativeDifferentials.idSquare
#check @SheafOfModules.RingedSite.RelativeDifferentials.map_id
#check @SheafOfModules.RingedSite.RelativeDifferentials.map_comp_coherent
