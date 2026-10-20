module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import ReasLib.RingTheory.Gorenstein.Local

@[expose] public section

universe u

/-- A commutative ring is Gorenstein if it is Noetherian and its localization at every
prime ideal is a Gorenstein local ring. -/
class IsGorensteinRing (R : Type u) [CommRing R] : Prop extends IsNoetherianRing R where
  /-- The localization at every prime ideal is a Gorenstein local ring. -/
  isGorensteinLocalRing_localization (p : Ideal R) [p.IsPrime] :
    IsGorensteinLocalRing (Localization.AtPrime p)

namespace IsGorensteinRing

variable (R : Type u) [CommRing R]

/-- Prime localizations of a Gorenstein ring are Gorenstein local rings. -/
instance instLocalizationAtPrime [h : IsGorensteinRing R] (p : Ideal R) [p.IsPrime] :
    IsGorensteinLocalRing (Localization.AtPrime p) :=
  h.isGorensteinLocalRing_localization p

/-- A Noetherian ring whose prime localizations are Gorenstein is Gorenstein. -/
theorem of_localizationAtPrime [IsNoetherianRing R]
    (h : ∀ (p : Ideal R) [p.IsPrime], IsGorensteinLocalRing (Localization.AtPrime p)) :
    IsGorensteinRing R := sorry

end IsGorensteinRing

/-- A commutative ring is Gorenstein exactly when it is Noetherian and all its prime
localizations are Gorenstein local rings. -/
theorem isGorensteinRing_iff (R : Type u) [CommRing R] :
    IsGorensteinRing R ↔
      IsNoetherianRing R ∧
        ∀ (p : Ideal R) [p.IsPrime], IsGorensteinLocalRing (Localization.AtPrime p) := sorry
