module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech.Vanishing
import StacksCheckRecall

@[expose] public section

/- Lemma 20.11.8 (01EV): vanishing positive Čech cohomology on every open covering implies
vanishing positive sheaf cohomology on every open. -/
@[stacks 01EV]
#check @AlgebraicGeometry.RingedSpace.ModuleCech.IsAcyclic.isZero_cohomology
#check @AlgebraicGeometry.RingedSpace.ModuleCech.IsAcyclic.isZero_module_cohomology
