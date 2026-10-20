/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.ReesAlgebra.Integral
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.38.1

This chapter entry recalls the reusable notion of integrality over an ideal.

@stack 00H2
-/

/- Definition 10.38.1 (Tag 00H2): an element is integral over an ideal when
it satisfies a monic equation with coefficients in the prescribed powers. -/
@[stacks 00H2]
#check @RingHom.IsIntegralOverIdeal

@[stacks 00H2 "monotonicity in the ideal"]
#check @RingHom.IsIntegralOverIdeal.mono
@[stacks 00H2 "top ideal specialization"]
#check @RingHom.isIntegralOverIdeal_top_iff
@[stacks 00H2 "bottom ideal specialization"]
#check @RingHom.isIntegralOverIdeal_bot_iff
