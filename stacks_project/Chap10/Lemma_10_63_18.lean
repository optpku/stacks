module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Regular
import StacksCheckRecall

/-!
# Lemma 10.63.18

@stack 00LL
-/

@[expose] public section

/- Lemma 10.63.18: an ideal in a Noetherian ring contains an element acting regularly on a finite
module exactly when it is not contained in any associated prime of that module. -/
@[stacks 00LL]
#check @Ideal.exists_isSMulRegular_iff_not_le_associatedPrimes
