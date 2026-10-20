/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.123.1 (Tag 00PQ): a polynomial relation makes the leading-coefficient multiple integral.

@stack 00PQ
-/

/- Lemma 10.123.1, tag 00PQ: a polynomial relation makes the
leading-coefficient multiple of the element integral. -/
@[stacks 00PQ]
#check @RingHom.isIntegralElem_leadingCoeff_mul
