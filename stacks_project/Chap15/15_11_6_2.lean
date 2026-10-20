/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Etale.QuotientSection
import StacksCheckRecall

/-!
# 15.11.6.2

@stack 0EM2
-/

@[expose] public section

/- 15.11.6.2 adds no separate algebraic object: it uses the canonical integral-closure product
decomposition controlled by the selected ideal's idempotent-lifting property. -/
@[stacks 0EM2 "integral-closure product decomposition"]
#check @Ideal.HasIntegralAlgebraIdempotentLifting.exists_integralClosureProductEquiv_of_etaleSection
