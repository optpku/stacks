/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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
