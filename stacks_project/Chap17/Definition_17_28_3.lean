module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Differentials
import StacksCheckRecall

@[expose] public section

/- Definition 17.28.3 (08RP): the module of relative differentials and its universal derivation
are owned on an arbitrary ringed site and specialize to sheaves on a topological space. -/
@[stacks 08RP]
#check @SheafOfModules.RingedSite.relativeDifferentials

#check @SheafOfModules.RingedSite.relativeDifferential
#check @TopCat.Sheaf.relativeDifferentials
#check @TopCat.Sheaf.relativeDifferential
