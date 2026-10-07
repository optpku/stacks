module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.37.2: the integral closure of a base ring in a normal domain is normal.

The statement is a direct specialization of the canonical integral-closure API.

@stack 034L
-/

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u v

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable [IsDomain S] [IsIntegrallyClosed S]

/- Lemma 10.37.2: if `S` is a normal domain, then the integral closure of `R` in `S` is a
normal domain. The primitive data here are only the canonical `R`-subalgebra
`integralClosure R S ⊆ S` and its inherited domain structure; the integrally closed conclusion is
derived, not packaged separately, and is exactly the owner theorem
`IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn` specialized to
`integralClosure R S ⊆ S`. Thus this item remains a direct canonical use of the upstream API,
rather than a parallel local wrapper. -/
@[stacks 034L]
#check IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn (integralClosure R S) S

end
