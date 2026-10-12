/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.ZeroDivisor
import StacksCheckRecall

/-!
# Lemma 10.63.9

@stack 00LD
-/

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.63.9 (Tag 00LD): for a Noetherian ring `R` and an `R`-module `M`, the union of the
exact-annihilator associated primes is the set of elements of `R` that are zero divisors on `M`.
-/
@[stacks 00LD]
#check @associatedPrimesOfModule.biUnion_eq_zero_divisors

@[stacks 00LD "complement of the zero-divisor union"]
#check @associatedPrimesOfModule.biUnion_eq_compl_regular
