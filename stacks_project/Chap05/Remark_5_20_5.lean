module

public import ReasLib.Topology.Specialization.Dimension.Obstruction
import StacksCheckRecall

@[expose] public section

/- Remark 5.20.5: the obstruction to a global dimension function is a class
in degree-one constant-sheaf cohomology. -/
@[stacks 02ID]
#check @TopologicalSpace.CatenarySpace.exists_dimensionFunction_obstructionClass
