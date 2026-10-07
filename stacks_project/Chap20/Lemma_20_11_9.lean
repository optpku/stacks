module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech.Cofinal
import StacksCheckRecall

@[expose] public section

/- Lemma 20.11.9 (01EW): a module with vanishing positive Čech cohomology on a
cofinal system of basis-stable covers has vanishing positive sheaf cohomology on basis opens. -/
@[stacks 01EW]
#check @AlgebraicGeometry.RingedSpace.ModuleCech.IsAcyclicOnBasis.isZero_cohomology

#check @AlgebraicGeometry.RingedSpace.ModuleCech.IsAcyclicOnBasis.isZero_module_cohomology
