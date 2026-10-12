/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Filtration
import StacksCheckRecall

/-!
# Lemma 10.63.4

@stack 00LB
-/

@[expose] public section

/- Lemma 10.63.4: every exact associated prime of a module occurs among the prime quotients in
any prime filtration from `0` to that module. -/
@[stacks 00LB]
#check @Module.PrimeFiltration.associatedPrimesOfModule_subset_range

@[stacks 00LB "associated-prime points in a filtration"]
#check @Module.PrimeFiltration.associatedPrimePoints_subset_primeFactors

@[stacks 00LB "associated-prime set in a filtration"]
#check @Module.PrimeFiltration.associatedPrimes_subset_range
