/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.RingTheory.Idempotent.Product
import StacksCheckRecall

@[expose] public section

universe u

/- Exercise 111.1.9: a ring `A` is isomorphic to a product of two nonzero rings if and
only if `A` has an idempotent other than `0` and `1`. -/
@[stacks 078G] #check
  (@RingEquiv.exists_prod_nontrivial_iff : ∀ {A : Type u} [CommRing A],
    (∃ (B : Type u) (C : Type u) (_ : CommRing B) (_ : CommRing C),
      Nontrivial B ∧ Nontrivial C ∧ Nonempty (A ≃+* B × C)) ↔
      ∃ e : A, IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1)
