module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak.Restriction
import StacksCheckRecall

/-!
# Weakly associated primes under finite restriction of scalars

@stack 05E1
-/

@[expose] public section

-- Lemma 10.66.13: for a finite ring map `R → S`, weakly associated primes commute with
-- restriction of scalars.
@[stacks 05E1]
#check @weaklyAssociatedPrimes.Restriction.eq_image_comap_of_finite
