module

import ReasLib.AlgebraicGeometry.Scheme.Module.ExternalTensor
import StacksCheckRecall

/- 57.13.1.1: the displayed left-infinite complex uses the canonical external tensor
   product term `externalTensorProduct`. -/
@[stacks 0G09] #check
  (AlgebraicGeometry.Scheme.Modules.externalTensorProduct :
    {X S Y : AlgebraicGeometry.Scheme} →
      (a : X ⟶ S) →
      (b : Y ⟶ S) →
      X.Modules →
      Y.Modules →
      (CategoryTheory.Limits.pullback a b).Modules)
