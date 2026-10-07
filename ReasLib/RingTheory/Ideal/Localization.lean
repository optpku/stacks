module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.Height

@[expose] public section

/-!
# Ideals at Prime Localizations

This leaf names the ideal and quotient obtained after localizing an ambient ring at a prime.
-/

universe u

namespace Ideal

variable {R : Type u} [CommRing R]

/-- The extension of an ideal to the localization of its ambient ring at a prime. -/
abbrev localizationAtPrime (I : Ideal R) (p : PrimeSpectrum R) :
    Ideal (Localization.AtPrime p.asIdeal) :=
  I.map (algebraMap R (Localization.AtPrime p.asIdeal))

/-- The quotient of a prime localization by the extension of an ambient ideal. -/
abbrev quotientAtPrime (I : Ideal R) (p : PrimeSpectrum R) : Type u :=
  Localization.AtPrime p.asIdeal ⧸ I.localizationAtPrime p

/-- If `I ⊆ p`, then the extension of `I` to `R_p` lies in the maximal ideal of `R_p`. -/
theorem localizationAtPrime_le_maximalIdeal (I : Ideal R) (p : PrimeSpectrum R)
    (hIp : I ≤ p.asIdeal) :
    I.localizationAtPrime p ≤ IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal) := sorry

end Ideal

/-- For comparable prime ideals `q ≤ p`, the Krull dimension of the localization at `p`
modulo the extension of `q` equals the height of the image of `p` in the quotient by `q`. -/
theorem ringKrullDim_quotientAtPrime_eq_height_map_quotient
    {A : Type u} [CommRing A] {p q : PrimeSpectrum A} (h : q ≤ p) :
    ringKrullDim (q.asIdeal.quotientAtPrime p) =
      (p.asIdeal.map (Ideal.Quotient.mk q.asIdeal)).height := sorry
