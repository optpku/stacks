/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.IntegralClosure.Subring
import StacksCheckRecall

/-!
# Definition 10.36.9

@stack 00GP
-/

@[expose] public section

/- Definition 10.36.9 (Tag 00GP): the integral closure and integrally closed
subring notions are the canonical Mathlib objects; the equality presentation
is supplied by `Subring.isIntegrallyClosedIn_iff_eq_integralClosure`. -/
@[stacks 00GP]
#check @integralClosure
#check @IsIntegrallyClosedIn

@[stacks 00GP]
#check @Subring.isIntegrallyClosedIn_iff_eq_integralClosure
