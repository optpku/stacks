module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.ExactSequence
import StacksCheckRecall

/-!
# Lemma 10.63.3

@stack 02M3
-/

@[expose] public section

/- Lemma 10.63.3 (1): exact associated primes are monotone under injective linear maps. -/
@[stacks 02M3 "(1)"]
#check @associatedPrimesOfModule.subset_of_injective

/- Lemma 10.63.3 (2): exact associated primes of the middle term of a short exact sequence come
from one of its outer terms. -/
@[stacks 02M3 "(2)"]
#check @associatedPrimesOfModule.subset_union_of_exact

/- Lemma 10.63.3 (3): exact associated primes of a binary direct sum form the union of those of
the summands. -/
@[stacks 02M3 "(3)"]
#check @associatedPrimesOfModule.prod
