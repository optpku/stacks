module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Serre
import StacksCheckRecall

@[expose] public section

/-!
# Embedded associated primes and Serre's condition

@stack 031Q

Lemma 10.157.2 is the source-facing instance of the canonical module theorem
`Module.embeddedAssociatedPrimes_eq_empty_iff_serreConditionS_one`.
-/

/- Lemma 10.157.2 (Stacks tag `031Q`): for a finite module over a Noetherian
ring, the absence of embedded associated primes is equivalent to Serre's
condition `(S_1)`. -/
@[stacks 031Q "Serre S1 criterion"]
#check @Module.embeddedAssociatedPrimes_eq_empty_iff_serreConditionS_one
#print axioms Module.embeddedAssociatedPrimes_eq_empty_iff_serreConditionS_one
