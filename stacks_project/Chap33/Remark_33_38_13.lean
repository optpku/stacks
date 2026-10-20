module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.DimensionOne
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Remark 33.38.13: if a scheme's reduction is Noetherian, separated, and has topological Krull
dimension one, then the scheme has an ample invertible module. -/
@[stacks 09P0] #check
  (AlgebraicGeometry.Scheme.Modules.hasAmpleInvertibleModule_of_reduction_dimension_one :
    ∀ {X : Scheme.{u}} [IsNoetherian X.reduction] [X.reduction.IsSeparated],
      topologicalKrullDim X.reduction = 1 →
        AlgebraicGeometry.Scheme.Modules.HasAmpleInvertibleModule X)
