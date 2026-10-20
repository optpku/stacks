/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.PrimeAvoidance
import StacksCheckRecall

@[expose] public section

universe u v

open scoped Pointwise

#check
  (Ideal.exists_add_not_mem_finset_primes :
    ∀ {R : Type u} [CommRing R] {ι : Type v} {x : R} {I : Ideal R} (s : Finset ι)
      (p : ι → Ideal R) (hp : ∀ i ∈ s, (p i).IsPrime)
      (hx : ∀ i ∈ s, ¬ (x +ᵥ (I : Set R)) ⊆ (p i : Set R)),
      ∃ y ∈ I, ∀ i ∈ s, x + y ∉ p i)

#check
  (Ideal.subset_union_prime :
    ∀ {R : Type u} [CommRing R] {ι : Type v} {s : Finset ι} {f : ι → Ideal R}
      (a b : ι) (hp : ∀ i ∈ s, i ≠ a → i ≠ b → (f i).IsPrime) {I : Ideal R},
      ((I : Set R) ⊆ ⋃ i ∈ (s : Set ι), f i) ↔ ∃ i ∈ s, I ≤ f i)

#check
  (Ideal.Quotient.mk_surjective :
    ∀ {R : Type u} [Ring R] {I : Ideal R} [I.IsTwoSided],
      Function.Surjective (Ideal.Quotient.mk I))

/- Lemma 33.42.5: any class modulo an ideal not contained in any of a finite family of prime
ideals has a representative outside every prime in the family. -/
@[stacks 09NK]
#check
  (Ideal.Quotient.exists_mk_eq_and_not_mem_fin_primes :
    ∀ {A : Type u} [CommRing A] (I : Ideal A) {r : ℕ} (primes : Fin r → Ideal A)
      (hprimes : ∀ i, (primes i).IsPrime) (hI : ∀ i, ¬ I ≤ primes i) (fbar : A ⧸ I),
      ∃ f : A, Ideal.Quotient.mk I f = fbar ∧ ∀ i, f ∉ primes i)
