/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.DifferentialOperator.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.133.2

@stack 09CJ

Lemma 10.133.2 (Tag 09CJ): if `D : L →ₗ[R] M` and `D' : M →ₗ[R] N` have
differential-operator orders at most `k` and `k'`, respectively, then
`D'.comp D` has order at most `k + k'`.

The reusable theorem is the predicate method
`LinearMap.IsDifferentialOperatorOfOrder.comp`; its hypotheses only require
the commuting scalar actions needed for scalar commutators.
-/

@[stacks 09CJ "composition of differential operators"]
#check @LinearMap.IsDifferentialOperatorOfOrder.comp

@[stacks 09CJ "order-bound composition"]
#check @differentialOperatorsOrderLE.comp
