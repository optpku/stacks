/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak
import StacksCheckRecall

@[expose] public section

/-!
# Minimal points of module support

@stack 05C4
-/

-- Lemma 10.66.8: a minimal point of a module's support is weakly associated to the module.
@[stacks 05C4]
#check @weaklyAssociatedPrimes.mem_of_minimal_support
