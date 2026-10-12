/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Support
import StacksCheckRecall

/-!
# Lemma 10.63.8

@stack 05BV
-/

@[expose] public section

/- Lemma 10.63.8 (Tag 05BV): a minimal point of module support over a Noetherian ring is an
associated prime.  The reusable theorem does not require the module to be finite. -/
@[stacks 05BV]
#check @Module.minimal_support_mem_associatedPrimes

/- Symmetric point-level companions used by filtration and dimension arguments. -/
@[stacks 05BV "minimal support point criterion"]
#check @associatedPrimes.minimal_point_iff_minimal_support

@[stacks 05BV "module-associated-prime point criterion"]
#check @associatedPrimesOfModule.minimal_point_iff_minimal_support
