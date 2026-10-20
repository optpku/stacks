/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Algebraic.StronglyTranscendental
import StacksCheckRecall

@[expose] public section

/-! @stack 00PZ -/

/- Definition 10.123.7 (Tag 00PZ): strong transcendence is the canonical
`IsStronglyTranscendental` predicate; its coefficientwise view is supplied by
the reusable `IsStronglyTranscendental` characterization API. -/
@[stacks 00PZ]
#check @IsStronglyTranscendental

@[stacks 00PZ]
#check @IsStronglyTranscendental.iff_mul_coeff_eq_zero
@[stacks 00PZ "coefficientwise vanishing"]
#check @IsStronglyTranscendental.mul_coeff_eq_zero
@[stacks 00PZ "coefficientwise converse"]
#check @IsStronglyTranscendental.of_mul_coeff_eq_zero
