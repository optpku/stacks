module

public import Mathlib.RingTheory.Ideal.Oka
import StacksCheckRecall

@[expose] public section

/-!
# Proposition 10.28.8

@stack 05KE
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Proposition 10.28.8: if `𝓕` is an Oka family of ideals of `R`, then any ideal maximal in the
complement of `𝓕` is prime. This is the canonical theorem
`Ideal.IsOka.isPrime_of_maximal_not`; by Definition 10.28.2, a set family
`𝓕 : Set (Ideal R)` is read as the predicate `fun I ↦ I ∈ 𝓕`. -/
@[stacks 05KE]
#check @Ideal.IsOka.isPrime_of_maximal_not
