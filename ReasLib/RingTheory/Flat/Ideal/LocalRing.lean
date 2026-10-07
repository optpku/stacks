module

public import ReasLib.Algebra.Module.SpanRankOperations
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Span

@[expose] public section

universe u

namespace IsLocalRing

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- A Noetherian local ring whose ideals are all flat modules is a domain and a
principal ideal ring. -/
theorem isDomain_and_isPrincipalIdealRing_of_forall_ideal_flat
    (hflat : ∀ I : Ideal A, Module.Flat A I) :
    IsDomain A ∧ IsPrincipalIdealRing A := sorry

end IsLocalRing
