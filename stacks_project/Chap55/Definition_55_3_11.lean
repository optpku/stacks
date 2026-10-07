module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.TopologicalGenus

/- Definition 55.3.11: the topological genus of a numerical type `T` is the
nonnegative integer represented by `1 - T.n + T.edgeCount`. -/
@[stacks 0C79] #check (NumericalType.topologicalGenus : NumericalType → ℕ)
