module

public import ReasLib.Topology.Sheaf.Cohomology.Bridge
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cohomology.Flasque
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

/- Lemma 20.12.3 (09SY): a flasque abelian sheaf has zero positive-degree cohomology on every
open.  The canonical instance API and the source-facing explicit-hypothesis bridge are owned by
`ReasLib.Topology.Sheaf.Cohomology.Bridge`; the module-valued specialization is in the companion
ReasLib leaf. -/
@[stacks 09SY]
#check @CategoryTheory.Sheaf.IsFlasque.isZero_cohomology

#check @CategoryTheory.Sheaf.higherCohomology_isZero_of_isFlasque
#check @AlgebraicGeometry.RingedSpace.ModuleCohomology.isZero_module_of_flasque
#check @AlgebraicGeometry.RingedSpace.ModuleCohomology.isZero_module_of_flasque'

