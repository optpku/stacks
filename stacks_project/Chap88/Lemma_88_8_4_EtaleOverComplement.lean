module

public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Ideal.Over

/-!
# Étale algebras over the complement of V(I)

The predicate `IsEtaleOverComplement I B` records that `Spec(B) → Spec(A)` is
étale over `Spec(A) \ V(I)`, equivalently that `B` is étale at every prime
outside `V(I B)`.
-/

@[expose] public section

universe u

namespace Algebra

variable {A : Type u} [CommRing A]

/-- The `A`-algebra `B` is étale over `Spec(A) \ V(I)`: every prime of `B`
outside `V(I B)` lies in the étale locus. -/
def IsEtaleOverComplement (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B] : Prop :=
  (PrimeSpectrum.zeroLocus (I.map (algebraMap A B) : Set B))ᶜ ⊆ etaleLocus A B

/-- Étaleness over `Spec(A) \ V(I)` means `B` is étale at every prime not
containing `I B`. -/
theorem isEtaleOverComplement_iff (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B] :
    IsEtaleOverComplement I B ↔
      ∀ (q : Ideal B) [q.IsPrime], ¬ I.map (algebraMap A B) ≤ q → IsEtaleAt A q :=
  sorry

/-- Étaleness over `Spec(A) \ V(I)` means `B` is étale at every prime whose
contraction to `A` does not contain `I`. -/
theorem isEtaleOverComplement_iff_under (I : Ideal A) (B : Type u) [CommRing B]
    [Algebra A B] :
    IsEtaleOverComplement I B ↔
      ∀ q : PrimeSpectrum B, ¬ I ≤ q.asIdeal.under A → IsEtaleAt A q.asIdeal :=
  sorry

namespace IsEtaleOverComplement

/-- Evaluate étaleness over `Spec(A) \ V(I)` at a prime not containing `I B`. -/
theorem apply {I : Ideal A} {B : Type u} [CommRing B] [Algebra A B]
    (h : IsEtaleOverComplement I B) {q : Ideal B} [q.IsPrime]
    (hq : ¬ I.map (algebraMap A B) ≤ q) :
    IsEtaleAt A q :=
  sorry

end IsEtaleOverComplement

end Algebra
