/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Derived.Composition.Basic
import StacksCheckRecall

@[expose] public section

noncomputable section

/- Equation 22.34.0.1 (0BZ2): the displayed map `N_B ⊗_Bᴸ N' ⟶ (N_B ⊗_B N')_C` is the
canonical counit component comparing derived and ordinary relative tensor products. -/
@[stacks 0BZ2] #check
  @DifferentialGradedBimodule.Tensor.Derived.ordinaryComparison

#check @DifferentialGradedBimodule.Tensor.derivedCounit
#check @DifferentialGradedBimodule.Tensor.obj
