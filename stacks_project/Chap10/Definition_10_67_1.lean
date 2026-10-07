module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Embedded
import StacksCheckRecall

@[expose] public section

/-!
# Embedded Associated Primes

This source-facing entry recalls the shared module and ring APIs for embedded
associated primes.

@stack 02M5
-/

-- Definition 10.67.1, tag `02M5`: the embedded associated primes of a module
-- are its nonminimal associated primes.
@[stacks 02M5]
#check @embeddedAssociatedPrimes
@[stacks 02M5 "embedded associated-prime membership"]
#check @mem_embeddedAssociatedPrimes_iff
@[stacks 02M5 "absence of embedded associated primes"]
#check @embeddedAssociatedPrimes_eq_empty_iff

-- Definition 10.67.1, tag `02M5`, ring specialization: embedded primes of a
-- ring are its embedded associated primes as a module over itself.
@[stacks 02M5 "embedded primes of a ring"]
#check @embeddedPrimes
@[stacks 02M5 "embedded-prime membership"]
#check @mem_embeddedPrimes_iff
@[stacks 02M5 "absence of embedded primes"]
#check @embeddedPrimes_eq_empty_iff
