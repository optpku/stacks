module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.LocallyFree.Flat
import StacksCheckRecall

@[expose] public section

/- Definition 17.17.1 (05ND): flat module sheaves on a ringed space. -/
@[stacks 05ND]
#check @SheafOfModules.IsFlat

#check @SheafOfModules.IsFlat.iff_forall_isFlatAt

#check @SheafOfModules.IsLocallyFree.isFlat
