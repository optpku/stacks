module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u v

open scoped Pointwise

namespace Ideal

/-- If a coset of an ideal is not contained in any prime of a finite family,
one element of the coset avoids the whole family. -/
@[stacks 0EHL]
theorem exists_add_not_mem_finset_primes {R : Type u} [CommRing R]
    {ι : Type v} {x : R} {I : Ideal R} (s : Finset ι) (p : ι → Ideal R)
    (hp : ∀ i ∈ s, (p i).IsPrime)
    (hx : ∀ i ∈ s, ¬ (x +ᵥ (I : Set R)) ⊆ (p i : Set R)) :
    ∃ y ∈ I, ∀ i ∈ s, x + y ∉ p i := sorry

/-- Every residue class has a representative outside a finite family of prime ideals
when the quotient ideal is contained in none of them. -/
@[stacks 09NK]
theorem Quotient.exists_mk_eq_and_not_mem_fin_primes {A : Type u} [CommRing A]
    (I : Ideal A) {r : ℕ} (primes : Fin r → Ideal A)
    (hprimes : ∀ i, (primes i).IsPrime) (hI : ∀ i, ¬ I ≤ primes i) (fbar : A ⧸ I) :
    ∃ f : A, Quotient.mk I f = fbar ∧ ∀ i, f ∉ primes i := sorry

/-- An ideal not contained in either of two prime ideals is not contained in their union. -/
theorem not_subset_union {A : Type u} [CommRing A] (I q1 q2 : Ideal A) [q1.IsPrime] [q2.IsPrime]
    (h1 : ¬ I ≤ q1) (h2 : ¬ I ≤ q2) :
    ¬ ((I : Set A) ⊆ (q1 : Set A) ∪ (q2 : Set A)) := sorry

/-- An ideal avoiding two prime ideals contains an element outside both primes. -/
theorem exists_mem_notMem {A : Type u} [CommRing A] (I q1 q2 : Ideal A) [q1.IsPrime] [q2.IsPrime]
    (h1 : ¬ I ≤ q1) (h2 : ¬ I ≤ q2) :
    ∃ x ∈ I, x ∉ q1 ∧ x ∉ q2 := sorry

end Ideal
