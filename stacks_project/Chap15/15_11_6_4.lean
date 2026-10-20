/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Etale.QuotientSection
import StacksCheckRecall

/-!
# 15.11.6.4

@stack 0EM4
-/

@[expose] public section

/- 15.11.6.4: integral-algebra idempotent lifting promotes the quotient section to a product
decomposition of the integral closure. -/
@[stacks 0EM4 "integral-closure product decomposition"]
#check @Ideal.HasIntegralAlgebraIdempotentLifting.exists_integralClosureProductEquiv_of_etaleSection
