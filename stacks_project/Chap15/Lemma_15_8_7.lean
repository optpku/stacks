module

public import ReasLib.RingTheory.FittingIdeal.LocalGenerators
import StacksCheckRecall

/-!
# Fitting ideals and local generators

@stack 07ZC
-/

-- Lemma 15.8.7: `Fit_k(M)` detects the number of generators at a prime, on the residue-field
-- fiber, and on a standard-open neighborhood.
@[stacks 07ZC "Fitting ideal criterion for local generators"]
#check @FittingIdeal.not_le_prime_tfae_finrank_and_generators
