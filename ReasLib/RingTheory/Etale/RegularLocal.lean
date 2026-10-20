module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReasLib.RingTheory.Etale.Noetherian
import Mathlib.Tactic.CrossRefAttribute
import ReasLib.RingTheory.Etale.Neighborhood.LocalConsequences
import ReasLib.RingTheory.RegularLocalRing.Fiber
import ReasLib.RingTheory.RegularLocalRing.Flat

/-!
# Regular local rings along etale maps

This leaf records the prime-local regularity equivalence for an etale algebra. The statement uses
the canonical prime localizations, so no separate lies-over witness is part of the API.

@stack 0AH0
-/

@[expose] public section

universe u v

namespace Algebra.Etale

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- For an étale algebra and a prime `q` of its target, the local ring at the contraction of `q`
is regular if and only if the local ring at `q` is regular. -/
@[stacks 0AH0 "regular local rings at corresponding etale primes"]
theorem localizationAtPrime_isRegularLocalRing_iff [Algebra.Etale A B]
    (q : PrimeSpectrum B) :
    IsRegularLocalRing (Localization.AtPrime (q.asIdeal.under A)) ↔
      IsRegularLocalRing (Localization.AtPrime q.asIdeal) := sorry
-- Proof strategy: combine `localizationAtPrime_isNoetherianRing_iff` with flat local descent and
-- ascent for regular local rings. For ascent, use an etale basic-open neighborhood of `q` to
-- identify the maximal-ideal quotient and prove that the canonical closed fiber is regular.

end Algebra.Etale

namespace RingHom.Etale

/-- An étale local homomorphism between Noetherian local rings preserves and reflects
regular-locality. -/
@[stacks 025N]
theorem isRegularLocalRing_iff
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    {f : A →+* B} [IsLocalHom f] (hf : f.Etale) :
    IsRegularLocalRing A ↔ IsRegularLocalRing B := sorry

end RingHom.Etale
