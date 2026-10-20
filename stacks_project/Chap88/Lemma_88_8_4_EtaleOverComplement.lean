module

public import ReasLib.RingTheory.Etale.Complement

/-! A source-facing bridge for the reusable étale complement API. -/

@[expose] public section

universe u

#check (Algebra.IsEtaleOverComplement :
  {A : Type u} → [CommRing A] → Ideal A → (B : Type u) → [CommRing B] →
    [Algebra A B] → Prop)

#check (Algebra.isEtaleOverComplement_iff :
  {A : Type u} → [CommRing A] → (I : Ideal A) → (B : Type u) → [CommRing B] →
    [Algebra A B] →
      (Algebra.IsEtaleOverComplement I B ↔
        ∀ (q : Ideal B) [q.IsPrime],
          ¬ I.map (algebraMap A B) ≤ q → Algebra.IsEtaleAt A q))

#check (Algebra.isEtaleOverComplement_iff_under :
  {A : Type u} → [CommRing A] → (I : Ideal A) → (B : Type u) → [CommRing B] →
    [Algebra A B] →
      (Algebra.IsEtaleOverComplement I B ↔
        ∀ q : PrimeSpectrum B, ¬ I ≤ q.asIdeal.under A → Algebra.IsEtaleAt A q.asIdeal))

#check (Algebra.IsEtaleOverComplement.apply :
  {A : Type u} → [CommRing A] → {I : Ideal A} → {B : Type u} → [CommRing B] →
    [Algebra A B] → Algebra.IsEtaleOverComplement I B → {q : Ideal B} →
      [q.IsPrime] → ¬ I.map (algebraMap A B) ≤ q → Algebra.IsEtaleAt A q)
