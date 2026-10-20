module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Empty
import StacksCheckRecall

/-!
# Lemma 10.63.7
@stack 0587
-/

@[expose] public section

/- Lemma 10.63.7 (Tag 0587): over a Noetherian ring, a module is zero exactly when its set of
exact-annihilator associated primes is empty.  The owner uses the canonical set-first orientation;
its symmetry is the source's displayed orientation. -/
@[stacks 0587]
#check @associatedPrimesOfModule.eq_empty_iff_subsingleton

/- The more general Mathlib-facing `CommSemiring` owner and the two exact directional APIs. -/
@[stacks 0587 "semiring associated-prime criterion"]
#check @associatedPrimes.eq_empty_iff_subsingleton

@[stacks 0587 "subsingleton associated-prime implication"]
#check @associatedPrimesOfModule.eq_empty_of_subsingleton

@[stacks 0587 "nonempty associated-prime implication"]
#check @associatedPrimesOfModule.nonempty
