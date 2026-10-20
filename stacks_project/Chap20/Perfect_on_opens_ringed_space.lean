module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Local
import StacksCheckRecall

@[expose] public section

/- Perfectness is detected by strictly perfect representatives on an open cover. -/
#check @AlgebraicGeometry.RingedSpace.CochainComplex.isPerfect_iff_exists_openCover
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.isPerfect_iff_exists_openCover
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.Perfect.ModelOn

