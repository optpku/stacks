module

public import ReasLib.RingTheory.Regular.Localization
import StacksCheckRecall

/-!
# Lemma 15.41.2 (Regular is a local property)

@stack 07C0
-/

@[expose] public section

/- Lemma 15.41.2 (Regular is a local property): for a ring map with Noetherian
target, global regularity, regularity at all target primes, and regularity at
all target maximal ideals are equivalent. -/
@[stacks 07C0] #check @RingHom.Regular.local_tfae

#check @RingHom.Regular.iff_atPrimes
#check @RingHom.Regular.iff_atMaximals
#check @RingHom.Regular.localizeAtPrime
