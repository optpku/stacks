/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.CrossRefAttribute

/-!
# Nested henselian pairs and quotients

@stack 0DYD

Henselianity along a chain of ideals is equivalent to henselianity at the smaller ideal together
with henselianity of the induced quotient pair.
-/

@[expose] public section

universe u

variable {A : Type u} [CommRing A]

/-- Lemma 15.11.9 (Stacks `0DYD`): for `I ≤ J`, the pair `(A, J)` is henselian exactly when
`(A, I)` and the quotient pair `(A ⧸ I, J / I)` are henselian. -/
@[stacks 0DYD]
theorem henselianRing_iff_henselianRing_and_quotient_henselianRing
    (I J : Ideal A) (hIJ : I ≤ J) :
    HenselianRing A J ↔
      HenselianRing A I ∧
        HenselianRing (A ⧸ I) (J.map (Ideal.Quotient.mk I)) := sorry
