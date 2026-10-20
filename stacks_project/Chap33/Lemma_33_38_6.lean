/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.DimensionOne
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 33.38.6: let `X` be a Noetherian integral separated scheme of dimension `1`. Then `X`
has an ample invertible sheaf. -/
@[stacks 09ND] #check
  (AlgebraicGeometry.Scheme.Modules.hasAmpleInvertibleModule_of_dimension_one :
    ∀ {X : AlgebraicGeometry.Scheme.{u}}, [AlgebraicGeometry.IsNoetherian X] →
      [AlgebraicGeometry.IsIntegral X] → [X.IsSeparated] →
        topologicalKrullDim X = 1 →
          AlgebraicGeometry.Scheme.Modules.HasAmpleInvertibleModule X)
