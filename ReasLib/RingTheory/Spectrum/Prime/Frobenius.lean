module

public import ReasLib.Algebra.CharP.Frobenius
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Frobenius on prime spectra

The prime-power endomorphism induces the identity on the prime spectrum of a
commutative ring in which the prime vanishes.
-/

@[expose] public section

universe u

namespace PrimeSpectrum

/-- The prime-power endomorphism of a commutative ring in which the prime vanishes
induces the identity map on its prime spectrum. -/
theorem comap_frobeniusOfPrime {R : Type u} [CommRing R] (p : ℕ) [Fact p.Prime]
    (hp : (p : R) = 0) :
    comap (RingHom.frobeniusOfPrime p hp) = id := sorry

/-- The map on prime spectra induced by the prime-power endomorphism fixes every point. -/
theorem comap_frobeniusOfPrime_apply {R : Type u} [CommRing R] (p : ℕ) [Fact p.Prime]
    (hp : (p : R) = 0) (x : PrimeSpectrum R) :
    comap (RingHom.frobeniusOfPrime p hp) x = x := sorry

end PrimeSpectrum
