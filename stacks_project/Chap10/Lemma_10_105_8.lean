module

public import ReasLib.RingTheory.Catenary.MinimalPrime
import StacksCheckRecall

/-!
# Catenarity and minimal-prime quotients

@stack 0AUP
-/

/- Lemma 10.105.8 (1): a Noetherian ring is catenary if and only if all of its
minimal-prime quotients are catenary. -/
@[stacks 0AUP "(1)"]
#check @isCatenaryRing_iff_forall_quotient_by_minimalPrime

/- Lemma 10.105.8 (2): a Noetherian ring is universally catenary if and only if all
of its minimal-prime quotients are universally catenary. -/
@[stacks 0AUP "(2)"]
#check @universallyCatenaryRing_iff_forall_quotient_by_minimalPrime
