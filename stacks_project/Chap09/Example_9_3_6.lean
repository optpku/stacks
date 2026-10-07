module

public import ReasLib.Geometry.Manifold.Complex.MeromorphicFunctionField
import StacksCheckRecall

@[expose] public section

open scoped Manifold Topology

universe u

/- Example 9.3.6 (Tag 09FL): for a connected complex one-manifold `X`, the meromorphic
functions modulo codiscrete equality form the field `ℂ(X)`. The reusable construction and its
representative API are owned by `Geometry.Manifold.Complex.MeromorphicFunctionField`. -/

section

variable (X : Type u) [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [ConnectedSpace X]

@[stacks 09FL]
#check MeromorphicFunctionField
#check (inferInstance : Field (MeromorphicFunctionField X))
#check MeromorphicFunctionField.mk_notMem_range_algebraMap_of_forall_not_eventuallyEq_const

end
