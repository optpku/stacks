/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.DifferentialOperator.TensorProduct
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.133.13 (Tag 0G37): tensoring an order-`k` differential operator on
the right preserves its order bound over the tensor-product algebra.

@stack 0G37

The general statement is owned by
`LinearMap.IsDifferentialOperatorOfOrder.rTensor`; this source file records
the textbook label without retaining a chapter-local tensor-action
implementation.
-/

@[stacks 0G37 "right tensor differential operator"]
#check @LinearMap.IsDifferentialOperatorOfOrder.rTensor
