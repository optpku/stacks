/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Quotient
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.63.14

@stack 05BY
-/

/- Lemma 10.63.14 (Stacks 05BY): exact associated primes of a quotient-ring
module, contracted to the base ring, agree with its restricted-scalar exact
associated primes. -/
@[stacks 05BY] #check @associatedPrimesOfModule.Quotient.image_comap_eq
