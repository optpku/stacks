module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak
import StacksCheckRecall

@[expose] public section

/-!
# Weakly associated primes of a reduced ring

@stack 0EMA
-/

-- Lemma 10.66.3: for a reduced ring `R`, the weakly associated primes of its regular module are
-- exactly its minimal primes.
@[stacks 0EMA]
#check @weaklyAssociatedPrimes.ring_eq_minimalPrimes
