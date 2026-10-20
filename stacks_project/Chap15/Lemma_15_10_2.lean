/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Jacobson.Idempotent
import StacksCheckRecall

/-!
# Lemma 15.10.2

@stack 09XF
-/

@[expose] public section

universe u

variable {A : Type u} [CommRing A]

-- Lemma 15.10.2 (09XF): a Zariski-pair quotient map is injective on idempotents.
@[stacks 09XF]
#check
  (quotientMk_injective_on_idempotents_of_le_jacobson :
    (I : Ideal A) → I ≤ Ring.jacobson A →
      Function.Injective (Ideal.Quotient.mk I).idempotentMap)
