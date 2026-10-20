module

public import ReasLib.RingTheory.RingHom.Syntomic.AtPrime

/-!
# Syntomicity at primes meeting a submonoid
-/

@[expose] public section

universe u v

namespace RingHom

/-- A ring homomorphism is syntomic at every prime of the target that meets a
given submonoid. -/
def SyntomicAtPrimesMeeting {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (M : Submonoid S) : Prop :=
  ∀ q : PrimeSpectrum S, ¬ M ≤ q.asIdeal.primeCompl → f.SyntomicAtPrime q

namespace SyntomicAtPrimesMeeting

/-- Syntomicity at primes meeting `M` is equivalent to: every non-syntomic prime
of the target is disjoint from `M`. -/
theorem iff {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (M : Submonoid S) :
    f.SyntomicAtPrimesMeeting M ↔
      ∀ q : PrimeSpectrum S, ¬ f.SyntomicAtPrime q → M ≤ q.asIdeal.primeCompl :=
  sorry

end SyntomicAtPrimesMeeting

end RingHom

end
