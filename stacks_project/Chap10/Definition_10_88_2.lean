/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.LinearAlgebra.TensorProduct.Domination

@[expose] public section

/-!
# Tensor-kernel domination

Definition 10.88.2 is recalled from `ReasLib.LinearAlgebra.TensorProduct.Domination`.
The shared owner is deliberately stated over commutative semirings, while the chapter uses its
commutative-ring specialization.

@stack 059B
-/

@[stacks 059B]
#check @LinearMap.Dominates

@[stacks 059B "domination characterization"]
#check @LinearMap.dominates_iff
