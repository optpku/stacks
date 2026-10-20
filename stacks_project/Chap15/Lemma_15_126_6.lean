/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Normal.PrincipalQuotient
import StacksCheckRecall

@[expose] public section

open IsNormalRing.ReducedPrincipalQuotient

/-!
# Lemma 15.126.6

@stack 0AXI

The source maximal-ideal statement and its stronger arbitrary-nonzero-element
form are both exposed by the normal principal-quotient leaf.
-/

/- Lemma 15.126.6: a nonzero maximal-ideal element divides a power of an element defining a
reduced principal quotient. -/
@[stacks 0AXI "Lemma 15.126.6, reduced principal quotient power bound"]
#check @exists_dvd_pow_of_mem_maximalIdeal

#check @exists_dvd_pow
