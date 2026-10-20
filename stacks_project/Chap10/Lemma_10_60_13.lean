/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.KrullDimension.PrincipalQuotient
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.60.13

@stack 00KW

The reusable principal-quotient dimension bounds are owned by
`ReasLib.RingTheory.KrullDimension.PrincipalQuotient`; this file only records the source views.
-/

/- Lemma 10.60.13 (1): if `x` lies in the maximal ideal, then
`dim R ≤ dim (R ⧸ Ideal.span {x}) + 1`. -/
@[stacks 00KW "(1)"]
#check @ringKrullDim_le_ringKrullDim_quotient_span_singleton_succ

/- Lemma 10.60.13 (2): if `x` also avoids every minimal prime, then the principal quotient
lowers Krull dimension by exactly one.  The canonical owner orients the equality with the
quotient dimension on the left. -/
@[stacks 00KW "(2)"]
#check @ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_notMem_minimalPrimes

/- The parenthetical nonzerodivisor example is the existing Mathlib specialization. -/
@[stacks 00KW "(2), nonzerodivisor specialization"]
#check @ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
