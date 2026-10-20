/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.DimensionOne
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Proposition 33.38.12: let `X` be a Noetherian separated scheme of dimension `1`. Then `X`
has an ample invertible sheaf. -/
@[stacks 09NZ] #check
  (AlgebraicGeometry.Scheme.Modules.hasAmpleInvertibleModule_of_noetherian_separated_dimension_one :
    ∀ {X : Scheme.{u}} [IsNoetherian X] [X.IsSeparated],
      topologicalKrullDim X = 1 → AlgebraicGeometry.Scheme.Modules.HasAmpleInvertibleModule X)
