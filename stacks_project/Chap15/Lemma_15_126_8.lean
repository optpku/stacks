module

public import ReasLib.RingTheory.Ideal.HilbertSamuel.MinimalPrime
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.126.8

@stack 0BWX

The top-dimensional minimal-prime locus and its parameter-quotient length
bound are both owned by ReasLib.
-/

/- Lemma 15.126.8: top-dimensional minimal primes are bounded by a parameter quotient length. -/
@[stacks 0BWX "Lemma 15.126.8, top-dimensional minimal-prime length bound"]
#check @IsLocalRing.IsSystemOfParameters.topDim_encard_le_length

#check @minimalPrimes.topDim
#check @minimalPrimes.mem_topDim_iff
