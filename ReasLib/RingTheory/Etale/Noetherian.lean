module

public import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.Tactic.CrossRefAttribute
import ReasLib.RingTheory.RingHom.FaithfullyFlat.Noetherian

/-!
# Noetherian local rings along etale maps

The canonical local map at a prime of an etale algebra is faithfully flat and essentially of
finite type. This leaf packages the resulting Noetherian ascent and descent equivalence.

@stack 0AGZ
-/

@[expose] public section

universe u v

namespace Algebra.Etale

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- For an étale algebra and a prime `q` of its target, localization at `q.asIdeal.under A` is
Noetherian if and only if localization at `q` is Noetherian. -/
@[stacks 0AGZ "Noetherianity at a prime of an etale algebra"]
theorem localizationAtPrime_isNoetherianRing_iff [Algebra.Etale A B]
    (q : PrimeSpectrum B) :
    IsNoetherianRing (Localization.AtPrime (q.asIdeal.under A)) ↔
      IsNoetherianRing (Localization.AtPrime q.asIdeal) := sorry
-- Proof strategy: give the prime-localization map its canonical local algebra structure. For
-- ascent, use `Algebra.EssFiniteType.of_comp` and
-- `Algebra.EssFiniteType.isNoetherianRing`; for descent, combine
-- `Module.FaithfullyFlat.of_flat_of_isLocalHom` with
-- `RingHom.FaithfullyFlat.isNoetherianRing`.

end Algebra.Etale
