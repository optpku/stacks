/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

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

/-- Deprecated compatibility spelling for `associatedPrimesOfModule.Restriction.eq_image_comap`.
New code should use the namespaced exact-associated-prime owner. -/
@[deprecated associatedPrimesOfModule.Restriction.eq_image_comap (since := "2026-08-07")]
theorem associatedPrimesOfModule_restrictScalars_eq_image_comap
    {S : Type*} [CommRing S] [Algebra R S] [Module S M] [IsScalarTower R S M]
    [IsNoetherianRing S] :
    Ideal.comap (algebraMap R S) '' associatedPrimesOfModule S M =
      associatedPrimesOfModule R M := sorry

namespace associatedPrimes.Restriction

/-- The radical-based associated-prime sets commute with restriction of scalars along a
Noetherian scalar ring. -/
@[stacks 05DZ]
theorem eq_image_comap
    {S : Type*} [CommRing S] [Algebra R S] [Module S M] [IsScalarTower R S M]
    [IsNoetherianRing S] :
    Ideal.comap (algebraMap R S) '' associatedPrimes S M = associatedPrimes R M := sorry

end associatedPrimes.Restriction

/-- Deprecated compatibility spelling for `associatedPrimes.Restriction.eq_image_comap`.
New code should use the namespaced radical-associated-prime owner. -/
@[deprecated associatedPrimes.Restriction.eq_image_comap (since := "2026-08-07")]
theorem associatedPrimes_restrictScalars_eq_image_comap
    {S : Type*} [CommRing S] [Algebra R S] [Module S M] [IsScalarTower R S M]
    [IsNoetherianRing S] :
    Ideal.comap (algebraMap R S) '' associatedPrimes S M = associatedPrimes R M := sorry

end
