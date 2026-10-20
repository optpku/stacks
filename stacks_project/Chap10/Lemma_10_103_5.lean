/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CohenMacaulay.Module.Quotient
import StacksCheckRecall

/-!
# Lemma 10.103.5

@stack 0C6G
-/

@[expose] public section

/-
Lemma 10.103.5 (Stacks tag `0C6G`).  The source statement is the standard
Cohen--Macaulay criterion for quotienting a finite module by a regular element
of the maximal ideal.  Its reusable owner is the shared `ReasLib` theorem
below; this chapter file is intentionally a labelled recall rather than a
second proof of the same criterion.
-/
@[stacks 0C6G]
#check @Module.CohenMacaulay.QuotSMulTop.iff_cohenMacaulay_of_mem_maximalIdeal
