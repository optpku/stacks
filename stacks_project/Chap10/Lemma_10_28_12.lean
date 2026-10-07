module

public import ReasLib.RingTheory.Ideal.NonZeroDivisors
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.28.12: an ideal maximal among those containing no nonzerodivisor is prime. If the ring is
nonzero and every nonzero prime ideal contains a nonzerodivisor, then the ring is a domain.

The first clause is the canonical maximal-disjoint criterion specialized to `nonZeroDivisors`; the
second clause and its symmetric companion are owned by `IsDomain`.

@stack 05KI
-/

@[stacks 05KI "(1), maximal ideal avoiding nonzerodivisors"]
#check @Ideal.isPrime_of_maximal_disjoint_nonZeroDivisors

@[stacks 05KI "(2), domain criterion"]
#check @IsDomain.of_prime_contains_nonZeroDivisor

@[stacks 05KI "domain criterion iff"]
#check @IsDomain.iff_prime_contains_nonZeroDivisor
