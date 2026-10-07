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
