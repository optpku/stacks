module

public import ReasLib.RingTheory.Catenary.DimensionFunction
public import ReasLib.RingTheory.KrullDimension.DimensionLEOne

/-!
# Dimension functions on one-dimensional spectra

The quotient Krull dimension is a dimension function on the spectrum of a domain of
dimension at most one, with explicit values in dimension one.
-/

@[expose] public section

universe u

namespace PrimeSpectrum

/-- The quotient Krull dimension is a dimension function on the spectrum of a domain of
dimension at most one. -/
instance instIsDimensionFunctionQuotientKrullDim
    {A : Type u} [CommRing A] [IsDomain A] [Ring.DimensionLEOne A] :
    IsDimensionFunction (quotientKrullDim : PrimeSpectrum A → ℤ) := sorry

namespace quotientKrullDim

/-- On a one-dimensional domain, the quotient Krull dimension is zero exactly at maximal
points. -/
theorem eq_zero_iff_isMaximal
    {A : Type u} [CommRing A] [IsDomain A] (hdim : ringKrullDim A = 1)
    (p : PrimeSpectrum A) :
    PrimeSpectrum.quotientKrullDim p = 0 ↔ p.asIdeal.IsMaximal := sorry

/-- On a one-dimensional domain, the quotient Krull dimension is one exactly at the generic
point. -/
theorem eq_one_iff_eq_bot
    {A : Type u} [CommRing A] [IsDomain A] (hdim : ringKrullDim A = 1)
    (p : PrimeSpectrum A) :
    PrimeSpectrum.quotientKrullDim p = 1 ↔ p = ⊥ := sorry

/-- On a one-dimensional domain, the quotient Krull dimension is a dimension function. -/
theorem isDimensionFunctionOfDimOneDomain
    {A : Type u} [CommRing A] [IsDomain A] (hdim : ringKrullDim A = 1) :
    IsDimensionFunction (PrimeSpectrum.quotientKrullDim : PrimeSpectrum A → ℤ) := sorry

end quotientKrullDim

end PrimeSpectrum
