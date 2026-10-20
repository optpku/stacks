/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Derived.Composition.AlgebraTensor
import StacksCheckRecall

@[expose] public section

noncomputable section

/- Equation 22.34.1.1 (0BZ4): the canonical map from the derived relative tensor of the two
algebra-tensor bimodules to the literal ground-ring triple tensor `A ⊗[R] (B ⊗[R] C)`. -/
@[stacks 0BZ4] #check
  @DifferentialGradedBimodule.Tensor.Derived.AlgebraTensor.comparison

#check @DifferentialGradedBimodule.Tensor.algebra
#check @DifferentialGradedBimodule.Tensor.AlgebraTensor.tripleRightModule
#check @DifferentialGradedBimodule.Tensor.AlgebraTensor.contraction
#check @DifferentialGradedBimodule.Tensor.Derived.AlgebraTensor.comparison_fac
