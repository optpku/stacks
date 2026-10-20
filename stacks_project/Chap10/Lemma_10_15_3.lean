module

public import ReasLib.RingTheory.Ideal.PrimeAvoidance
import StacksCheckRecall

@[expose] public section

universe u v

open scoped Pointwise

/-!
# Lemma 10.15.3
@stack 0EHL

The finite-family coset avoidance statement is retained as a source-facing bridge.  The finite
prime-union criterion used by its induction is owned by `Ideal.subset_union_prime`.
-/

/- Lemma 10.15.3: a translate of a coset can avoid a finite family of prime ideals. -/
@[stacks 0EHL]
#check (Ideal.exists_add_not_mem_finset_primes :
  ∀ {R : Type u} [CommRing R] {ι : Type v} {x : R} {I : Ideal R}
    (s : Finset ι) (p : ι → Ideal R),
    (∀ i ∈ s, (p i).IsPrime) →
    (∀ i ∈ s, ¬ (x +ᵥ (I : Set R)) ⊆ (p i : Set R)) →
    ∃ y ∈ I, ∀ i ∈ s, x + y ∉ p i)

@[stacks 0EHL "finite prime-union owner"]
#check @Ideal.subset_union_prime
