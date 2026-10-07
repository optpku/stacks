module

public import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Zero loci of finitely generated ideals

This file records the intersection formula for zero loci in the orientation used for
successive support conditions.
-/

@[expose] public section

universe u

namespace PrimeSpectrum

variable {A : Type u} [CommRing A]

/-- The intersection of the zero loci of two finitely generated ideals is the zero locus of
their supremum. -/
theorem zeroLocus_inter_of_fg (I J : Ideal A) (hI : I.FG) (hJ : J.FG) :
    zeroLocus I ∩ zeroLocus J = zeroLocus ((I ⊔ J : Ideal A) : Set A) := sorry

end PrimeSpectrum
