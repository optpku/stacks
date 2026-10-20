module

public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import ReasLib.RingTheory.AbsolutelyIntegrallyClosed

@[expose] public section

/-!
# Quotients of absolutely integrally closed rings

@stack 0DCN
-/

universe u

namespace IsAbsolutelyIntegrallyClosed

variable {A : Type u} [CommRing A]

/-- Quotients of absolutely integrally closed rings are absolutely integrally
closed. This is a global instance because the quotient ring is canonical. -/
@[stacks 0DCN "absolute integral closedness of quotients"]
instance quotient (I : Ideal A) [IsAbsolutelyIntegrallyClosed A] :
    IsAbsolutelyIntegrallyClosed (A ⧸ I) := sorry
-- Proof strategy: lift the quotient polynomial with
-- `Polynomial.lifts_and_natDegree_eq_and_monic`, split the monic lift via
-- `IsAbsolutelyIntegrallyClosed.splits`, and map the factorization through `Ideal.Quotient.mk`.

end IsAbsolutelyIntegrallyClosed
