module

public import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Adic completeness from a complete quotient

@stack 0DYC

This leaf lifts completeness for one adic topology from a complete quotient
of a ring already complete for another adic topology.
-/

universe u

namespace IsAdicComplete

/-- Lemma 10.97.10 (0DYC): if a Noetherian ring is `I`-adically complete and
its quotient by `I` is complete for the image of `J`, then the ring is
`J`-adically complete. -/
@[stacks 0DYC]
theorem of_quotient
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {I J : Ideal A}
    (hA : IsAdicComplete I A)
    (hquot : IsAdicComplete (J.map (Ideal.Quotient.mk I)) (A ⧸ I)) :
    IsAdicComplete J A := sorry

end IsAdicComplete
