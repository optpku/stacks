/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.RingTheory.Sequence.Independence

universe u

/- Lemma 51.17.2: if a finite family ending in `f * g` is independent, then replacing
the last entry by `f` leaves it independent. -/
@[stacks 0EBW]
#check
  (RingTheory.Sequence.IsIndependent.snoc_left_of_mul :
    {A : Type u} → [CommRing A] → {n : ℕ} → {fs : Fin n → A} → {f g : A} →
      RingTheory.Sequence.IsIndependent (Fin.snoc fs (f * g)) →
        RingTheory.Sequence.IsIndependent (Fin.snoc fs f))
