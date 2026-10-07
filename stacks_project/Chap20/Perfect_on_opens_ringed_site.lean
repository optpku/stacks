module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
import StacksCheckRecall

@[expose] public section

/- Perfectness on a ringed space is definitionally the canonical opens-ringed-site property. -/
#check @AlgebraicGeometry.RingedSpace.CochainComplex.perfect
#check @RingedSite.CochainComplex.perfect
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.perfect
#check @RingedSite.Hom.ModuleDerived.perfect

