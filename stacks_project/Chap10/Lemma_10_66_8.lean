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
