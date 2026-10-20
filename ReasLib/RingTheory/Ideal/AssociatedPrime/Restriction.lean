module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Module
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Exact associated primes under restriction of scalars
-/

universe u v

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

namespace associatedPrimesOfModule.Restriction

/-- Contracting exact associated primes along a scalar tower is exact when the larger scalar
ring is Noetherian. -/
@[stacks 05DZ]
theorem eq_image_comap
    {S : Type*} [CommRing S] [Algebra R S] [Module S M] [IsScalarTower R S M]
    [IsNoetherianRing S] :
    Ideal.comap (algebraMap R S) '' associatedPrimesOfModule S M =
      associatedPrimesOfModule R M := sorry

end associatedPrimesOfModule.Restriction

namespace associatedPrimes.Restriction

/-- The radical-based associated-prime sets commute with restriction of scalars along a
Noetherian scalar ring. -/
@[stacks 05DZ]
theorem eq_image_comap
    {S : Type*} [CommRing S] [Algebra R S] [Module S M] [IsScalarTower R S M]
    [IsNoetherianRing S] :
    Ideal.comap (algebraMap R S) '' associatedPrimes S M = associatedPrimes R M := sorry

end associatedPrimes.Restriction

end
