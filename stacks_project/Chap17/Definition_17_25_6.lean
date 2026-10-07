module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.InvertiblePower.Comparison
import StacksCheckRecall

@[expose] public section

/- Definition 17.25.6 (01CU): integral tensor powers of an invertible module sheaf are the
integer powers of its tensor-right autoequivalence, evaluated at the structure module. -/
@[stacks 01CU]
#check @AlgebraicGeometry.RingedSpace.InvertiblePower.sheaf

#check @AlgebraicGeometry.RingedSpace.InvertiblePower.zeroIso
#check @AlgebraicGeometry.RingedSpace.InvertiblePower.succIso
#check @AlgebraicGeometry.RingedSpace.InvertiblePower.negOneIso
#check @AlgebraicGeometry.RingedSpace.InvertiblePower.negSuccIso
#check @AlgebraicGeometry.RingedSpace.InvertiblePower.oneAddIso
#check @AlgebraicGeometry.RingedSpace.InvertiblePower.addIso
