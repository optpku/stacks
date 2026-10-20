module

public import Mathlib.RingTheory.Spectrum.Prime.Polynomial
public import ReasLib.RingTheory.Spectrum.Prime.BasicOpen

@[expose] public section

universe u

namespace Polynomial

/-- The image of the principal basic open of a polynomial under contraction
is the union of the principal basic opens of all of its coefficients. -/
theorem image_comap_C_basicOpen_eq_iUnion {A : Type u} [CommRing A] (f : A[X]) :
    PrimeSpectrum.comap Polynomial.C ''
        (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A[X])) =
      ⋃ i : ℕ, (PrimeSpectrum.basicOpen (f.coeff i) : Set (PrimeSpectrum A)) := sorry

end Polynomial
