module

public import ReasLib.RingTheory.Etale.ElementaryLocalization
import StacksCheckRecall

universe u v w x

/- Definition 38.6.1: an elementary étale localization of `f : R →+* S` at a prime
`q` over `p` is a commutative square with étale horizontal maps, compatible primes,
and bijective canonical maps on residue fields. -/
@[stacks 05HW] #check (RingHom.ElementaryEtaleLocalization.{u, v, w, x} :
  {R : Type u} → {S : Type v} → [CommRing R] → [CommRing S] →
    (f : R →+* S) → (p : PrimeSpectrum R) → (q : PrimeSpectrum S) →
      p.asIdeal = q.asIdeal.comap f →
        Type (max (max (max u v) (w + 1)) (x + 1)))
