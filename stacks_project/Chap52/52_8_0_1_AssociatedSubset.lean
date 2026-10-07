module

public import ReasLib.RingTheory.Spectrum.Prime.AssociatedSubset

@[expose] public section

universe u

#check (PrimeSpectrum.associatedSubset :
  {A : Type u} → [CommRing A] → Ideal A → Ideal A → Set (PrimeSpectrum A))
