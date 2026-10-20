/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Sequence.Independence
import StacksCheckRecall

universe u

/- Lemma 51.17.3: for an independent finite family ending in `f * g`, finite length
of its quotient makes that length the sum of the quotient lengths obtained using `f` and `g`. -/
@[stacks 0EBX] #check (RingTheory.Sequence.IsIndependent.length_quotient_snoc_mul :
  ∀ {A : Type u} [CommRing A] {n : ℕ} {fs : Fin n → A} {f g : A},
    RingTheory.Sequence.IsIndependent (Fin.snoc fs (f * g)) →
    IsFiniteLength A (A ⧸ Ideal.span (Set.range (Fin.snoc fs (f * g)))) →
    Module.length A (A ⧸ Ideal.span (Set.range (Fin.snoc fs (f * g)))) =
      Module.length A (A ⧸ Ideal.span (Set.range (Fin.snoc fs f))) +
        Module.length A (A ⧸ Ideal.span (Set.range (Fin.snoc fs g))))
