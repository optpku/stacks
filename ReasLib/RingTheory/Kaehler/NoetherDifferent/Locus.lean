module

public import Mathlib.RingTheory.Unramified.Locus
public import ReasLib.RingTheory.Kaehler.NoetherDifferent

@[expose] public section

universe u v

namespace KaehlerDifferential

/-- For a finite type commutative algebra, the zero locus of the Noether different is
the locus of primes where the algebra is not unramified. -/
theorem zeroLocus_noetherDifferent
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B] :
    PrimeSpectrum.zeroLocus (noetherDifferent A B) =
      (Algebra.unramifiedLocus A B)ᶜ := sorry

end KaehlerDifferential
