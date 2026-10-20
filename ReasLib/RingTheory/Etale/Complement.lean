/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Ideal.Over

/-!
# Étale algebras over the complement of a closed set
-/

@[expose] public section

universe u

namespace Algebra

variable {A : Type u} [CommRing A]

/-- The `A`-algebra `B` is étale over the complement of `V(I)` in `Spec A`. -/
def IsEtaleOverComplement (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B] : Prop :=
  (PrimeSpectrum.zeroLocus (I.map (algebraMap A B) : Set B))ᶜ ⊆ etaleLocus A B

/-- Étaleness over the complement of `V(I)` is equivalent to étaleness at every
prime of `B` that does not contain the extended ideal. -/
theorem isEtaleOverComplement_iff (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B] :
    IsEtaleOverComplement I B ↔
      ∀ (q : Ideal B) [q.IsPrime], ¬ I.map (algebraMap A B) ≤ q → IsEtaleAt A q :=
  sorry

/-- Étaleness over the complement of `V(I)` is equivalent to étaleness at every
prime whose contraction to `A` does not contain `I`. -/
theorem isEtaleOverComplement_iff_under (I : Ideal A) (B : Type u) [CommRing B]
    [Algebra A B] :
    IsEtaleOverComplement I B ↔
      ∀ q : PrimeSpectrum B, ¬ I ≤ q.asIdeal.under A → IsEtaleAt A q.asIdeal :=
  sorry

namespace IsEtaleOverComplement

/-- Evaluate étaleness over the complement of `V(I)` at a prime outside the
extended ideal. -/
theorem apply {I : Ideal A} {B : Type u} [CommRing B] [Algebra A B]
    (h : IsEtaleOverComplement I B) {q : Ideal B} [q.IsPrime]
    (hq : ¬ I.map (algebraMap A B) ≤ q) :
    IsEtaleAt A q :=
  sorry

end IsEtaleOverComplement

end Algebra
