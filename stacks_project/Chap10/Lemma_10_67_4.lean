/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Embedded
import StacksCheckRecall

/-!
# The annihilator quotient has no embedded primes

@stack 02M8
-/

@[expose] public section

/- Lemma 10.67.4: if a finite module over a Noetherian ring has no embedded
associated primes, then its annihilator quotient has no embedded primes. -/
@[stacks 02M8]
#check @embeddedAssociatedPrimes.quotient_annihilator_eq_empty
