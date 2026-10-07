module

public import ReasLib.RingTheory.Ideal.PrimeAvoidance
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.15.3
@stack 0EHL

The finite-family coset avoidance statement is retained as a source-facing bridge.  The finite
prime-union criterion used by its induction is owned by `Ideal.subset_union_prime`.
-/

/- Lemma 10.15.3: a translate of a coset can avoid a finite family of prime ideals. -/
@[stacks 0EHL]
#check @Ideal.exists_add_not_mem_finset_primes

@[stacks 0EHL "finite prime-union owner"]
#check @Ideal.subset_union_prime
