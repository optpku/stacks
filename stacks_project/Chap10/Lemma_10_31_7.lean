/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Algebra.TensorProduct.Noetherian
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.31.7

@stack 0CY6
-/

/- Lemma 10.31.7: finite-type base change of a Noetherian algebra is
Noetherian, in the tensor order used by the source. -/
@[stacks 0CY6]
#check @Algebra.FiniteType.isNoetherianRing_tensor_left
