module

public import ReasLib.RingTheory.Spectrum.Prime.Frobenius
import StacksCheckRecall

@[expose] public section

universe u

/- Exercise 111.62.5 (Frobenius) (1): if `p` is prime and `(p : R) = 0`, then
`RingHom.frobeniusOfPrime p hp : R →+* R` is the ring homomorphism `x ↦ x ^ p`. -/
@[stacks 0FWP] #check
  (RingHom.frobeniusOfPrime :
    ∀ {R : Type u} [CommRing R] (p : ℕ) [Fact p.Prime] (hp : (p : R) = 0), R →+* R)

#check
  (RingHom.frobeniusOfPrime_apply :
    ∀ {R : Type u} [CommRing R] (p : ℕ) [Fact p.Prime] (hp : (p : R) = 0) (x : R),
      RingHom.frobeniusOfPrime p hp x = x ^ p)

/- Exercise 111.62.5 (Frobenius) (2): if `p` is prime and `(p : R) = 0`, then
`PrimeSpectrum.comap (RingHom.frobeniusOfPrime p hp)` is the identity map on
`PrimeSpectrum R`. -/
@[stacks 0FWP] #check
  (PrimeSpectrum.comap_frobeniusOfPrime :
    ∀ {R : Type u} [CommRing R] (p : ℕ) [Fact p.Prime] (hp : (p : R) = 0),
      PrimeSpectrum.comap (RingHom.frobeniusOfPrime p hp) = id)

#check
  (PrimeSpectrum.comap_frobeniusOfPrime_apply :
    ∀ {R : Type u} [CommRing R] (p : ℕ) [Fact p.Prime] (hp : (p : R) = 0)
      (x : PrimeSpectrum R), PrimeSpectrum.comap (RingHom.frobeniusOfPrime p hp) x = x)
