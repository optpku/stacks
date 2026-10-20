/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.LinearAlgebra.TensorProduct.Domination.Pushout

/-!
# Pushout criterion for tensor-kernel domination

@stack 0AUM
-/

@[expose] public section

/- Lemma 10.88.4 is owned by the reusable pushout API for tensor-kernel domination. -/

@[stacks 0AUM]
#check @LinearMap.Dominates.iff_universallyInjective_pushoutInr
