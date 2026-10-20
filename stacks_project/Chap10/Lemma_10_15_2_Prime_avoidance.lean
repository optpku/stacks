/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Operations
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.15.2 (Prime avoidance)

@stack 00DS
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.15.2 (Prime avoidance): the canonical prime avoidance theorem states that if an ideal
is contained in the union of finitely many ideals and all but at most two of them are prime, then
it is contained in one of those ideals. Applied contrapositively to `J`, this yields an element of
`J` lying outside every `I_i`. -/
@[stacks 00DS]
#check @Ideal.subset_union_prime
