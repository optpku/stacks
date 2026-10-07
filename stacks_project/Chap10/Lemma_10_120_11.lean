module

public import Mathlib.RingTheory.Polynomial.RationalRoot
import StacksCheckRecall

/-!
# Unique factorization domains are normal

@stack 0AFV
-/

@[expose] public section

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]

/- Lemma 10.120.11 (Stacks `0AFV`): a unique factorization domain is normal, expressed by
Mathlib's canonical integral-closedness instance. -/
@[stacks 0AFV]
#check (UniqueFactorizationMonoid.instIsIntegrallyClosed : IsIntegrallyClosed R)
