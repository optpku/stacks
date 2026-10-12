/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Sequence.Independence

public section

universe u

namespace RingTheory.Sequence


#check
  (RingTheory.Sequence.IsIndependent :
    {A : Type u} → [CommRing A] → {n : ℕ} → (Fin n → A) → Prop)

#check
  (RingTheory.Sequence.isIndependent_iff :
    {A : Type u} → [CommRing A] → {n : ℕ} → (f : Fin n → A) →
      RingTheory.Sequence.IsIndependent f ↔
        ∀ a : Fin n → A, (∑ i, a i * f i) = 0 →
          ∀ i, a i ∈ Ideal.span (Set.range f))

#check
  (RingTheory.Sequence.IsIndependent.coeff_mem :
    {A : Type u} → [CommRing A] → {n : ℕ} → {f : Fin n → A} →
      RingTheory.Sequence.IsIndependent f →
        {a : Fin n → A} → (∑ i, a i * f i) = 0 → (i : Fin n) →
          a i ∈ Ideal.span (Set.range f))

#check
  (RingTheory.Sequence.IsIndependent.snoc_left_of_mul :
    {A : Type u} → [CommRing A] → {n : ℕ} → {fs : Fin n → A} → {f g : A} →
      RingTheory.Sequence.IsIndependent (Fin.snoc fs (f * g)) →
        RingTheory.Sequence.IsIndependent (Fin.snoc fs f))

end RingTheory.Sequence
