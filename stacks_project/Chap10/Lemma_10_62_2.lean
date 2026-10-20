module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Filtration
import StacksCheckRecall

/-!
# Lemma 10.62.2

@stack 00L4
-/

@[expose] public section

/- Lemma 10.62.2: the support of a module is the union of the zero loci of the factors in any
prime filtration from `0` to the whole module. -/
@[stacks 00L4]
#check @Module.PrimeFiltration.support_eq_iUnion_zeroLocus

@[stacks 00L4 "prime factors lie in the support"]
#check @Module.PrimeFiltration.primeFactors_subset_support
