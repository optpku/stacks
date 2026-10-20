/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.InverseSystem
import StacksCheckRecall

/-!
# Lemma 10.98.2

@stack 09B8
-/

@[expose] public section

/- Lemma 10.98.2 (09B8): under surjective successor maps with kernel
`I ^ n • ⊤`, the quotient of the inverse limit by `I ^ n` is canonically the
`n`th stage.  The general positive inverse-system API also gives its adic
completeness consequence. -/
@[stacks 09B8]
#check @CategoryTheory.PNatInverseSystem.limitProjectionQuotientEquiv

@[stacks 09B8 "quotient-stage equivalence application"]
#check @CategoryTheory.PNatInverseSystem.limitProjectionQuotientEquiv_apply_mk

@[stacks 09B8 "successive ideal-power completeness"]
#check @CategoryTheory.PNatInverseSystem.isAdicComplete_limit_of_successiveIdealPowerQuotients
