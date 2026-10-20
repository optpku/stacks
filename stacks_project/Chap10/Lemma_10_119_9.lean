/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.QuotSMulTop.FiniteLength
import StacksCheckRecall

/-!
# Lengths of Principal Quotients of Fraction-Field Submodules

@stack 00PE
-/

/- Lemma 10.119.9 (1): in a one-dimensional local domain, quotienting by a
nonzero element gives a finite-length scalar quotient. The reusable owner is
stated for any nonzerodivisor in a ring of Krull dimension at most one. -/
@[stacks 00PE "(1)"]
#check @isFiniteLength_quotient_span_singleton

/- Lemma 10.119.9 (2): the length of `M / xM` is bounded by the ambient
fraction-field dimension times the length of `R / (x)`. -/
@[stacks 00PE "(2)"]
#check @QuotSMulTop.length_le_finrank_mul_length_quotient_span_singleton
