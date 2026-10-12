/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Support
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Module

@[expose] public section

/-!
# Weakly Associated Primes of Modules

This module defines weak association for modules in terms of minimal primes over element
annihilators. The pointwise predicate lives in the `Ideal` namespace, and the set-valued owner is
`weaklyAssociatedPrimes`.
-/

universe u v

namespace Ideal

/-- A prime ideal `𝔭` is weakly associated to the `R`-module `M` when it is minimal over
the annihilator ideal of an element of `M`. -/
@[stacks 0547]
def IsWeaklyAssociatedToModule (R : Type u) (M : Type v)
    [CommRing R] [AddCommGroup M] [Module R M] (𝔭 : Ideal R) : Prop :=
  ∃ m : M, 𝔭 ∈ (torsionOf R M m).minimalPrimes

/-- A weakly associated ideal of a module is prime. -/
theorem IsWeaklyAssociatedToModule.isPrime {R : Type u} {M : Type v}
    [CommRing R] [AddCommGroup M] [Module R M] {𝔭 : Ideal R}
    (h𝔭 : IsWeaklyAssociatedToModule R M 𝔭) :
    𝔭.IsPrime := sorry

end Ideal

/-- The set of weakly associated prime ideals of the `R`-module `M`. -/
@[stacks 0547]
def weaklyAssociatedPrimes (R : Type u) (M : Type v)
    [CommRing R] [AddCommGroup M] [Module R M] : Set (Ideal R) :=
  Ideal.IsWeaklyAssociatedToModule R M

/-- Membership in `weaklyAssociatedPrimes` is weak association to the module. -/
@[simp]
theorem mem_weaklyAssociatedPrimes_iff {R : Type u} {M : Type v}
    [CommRing R] [AddCommGroup M] [Module R M] (𝔭 : Ideal R) :
    𝔭 ∈ weaklyAssociatedPrimes R M ↔ Ideal.IsWeaklyAssociatedToModule R M 𝔭 := sorry

namespace weaklyAssociatedPrimes

/-- An element of the weakly associated-prime set carries its primality instance. -/
instance instIsPrime {R : Type u} {M : Type v}
    [CommRing R] [AddCommGroup M] [Module R M]
    (𝔭 : weaklyAssociatedPrimes R M) :
    𝔭.1.IsPrime := sorry

/-- The weakly associated-prime set of a subsingleton module is empty. -/
theorem eq_empty_of_subsingleton {R : Type u} {M : Type v}
    [CommRing R] [AddCommGroup M] [Module R M] [Subsingleton M] :
    weaklyAssociatedPrimes R M = ∅ := sorry

/-- A nontrivial module has a weakly associated prime. -/
theorem nonempty {R : Type u} {M : Type v}
    [CommRing R] [AddCommGroup M] [Module R M] [Nontrivial M] :
    (weaklyAssociatedPrimes R M).Nonempty := sorry

/-- The weakly associated-prime set is empty exactly when the module is subsingleton. -/
@[stacks 0588 "empty weakly associated-prime set"]
theorem eq_empty_iff_subsingleton {R : Type u} {M : Type v}
    [CommRing R] [AddCommGroup M] [Module R M] :
    weaklyAssociatedPrimes R M = ∅ ↔ Subsingleton M := sorry

/-- Weakly associated primes commute with restriction of scalars along a quotient map. -/
@[stacks 05C8]
theorem image_comap_quotient_eq {R : Type u} [CommRing R]
    (I : Ideal R) {M : Type v} [AddCommGroup M] [Module (R ⧸ I) M] [Module R M]
    [IsScalarTower R (R ⧸ I) M] :
    Ideal.comap (algebraMap R (R ⧸ I)) '' weaklyAssociatedPrimes (R ⧸ I) M =
      weaklyAssociatedPrimes R M := sorry

/-- Over a reduced ring, the weakly associated primes of the regular module are exactly the
minimal primes. -/
@[stacks 0EMA]
theorem ring_eq_minimalPrimes {R : Type u} [CommRing R] [IsReduced R] :
    weaklyAssociatedPrimes R R = minimalPrimes R := sorry

/-- A minimal point of a module's support is weakly associated to that module. -/
@[stacks 05C4]
theorem mem_of_minimal_support {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (p : PrimeSpectrum R) (hp : Minimal (· ∈ Module.support R M) p) :
    p.asIdeal ∈ weaklyAssociatedPrimes R M := sorry

end weaklyAssociatedPrimes

namespace LinearEquiv

/-- A linear equivalence identifies the weakly associated-prime sets of its source and target. -/
theorem weaklyAssociatedPrimes_eq
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    {N' : Type*} [AddCommGroup N'] [Module A N']
    (e : N ≃ₗ[A] N') :
    weaklyAssociatedPrimes A N = weaklyAssociatedPrimes A N' := sorry

end LinearEquiv

namespace IsAssociatedPrime

/-- A radical-based associated prime is weakly associated to the same module. -/
theorem isWeaklyAssociatedToModule {R : Type u} {M : Type v}
    [CommRing R] [AddCommGroup M] [Module R M] {𝔭 : Ideal R}
    (h𝔭 : IsAssociatedPrime 𝔭 M) :
    Ideal.IsWeaklyAssociatedToModule R M 𝔭 := sorry

end IsAssociatedPrime

namespace Ideal

/-- An exact-annihilator associated prime is weakly associated to the same module. -/
theorem IsAssociatedToModule.isWeaklyAssociatedToModule {R : Type u} {M : Type v}
    [CommRing R] [AddCommGroup M] [Module R M] {𝔭 : Ideal R}
    (h𝔭 : IsAssociatedToModule R M 𝔭) :
    IsWeaklyAssociatedToModule R M 𝔭 := sorry

/-- A weakly associated prime, viewed as a point of `Spec R`, belongs to the module support. -/
theorem IsWeaklyAssociatedToModule.mem_support {R : Type u} {M : Type v}
    [CommRing R] [AddCommGroup M] [Module R M] {𝔭 : Ideal R}
    (h𝔭 : IsWeaklyAssociatedToModule R M 𝔭) :
    (⟨𝔭, h𝔭.isPrime⟩ : PrimeSpectrum R) ∈ Module.support R M := sorry

end Ideal

namespace associatedPrimesOfModule

/-- Exact-annihilator associated primes are weakly associated. -/
@[stacks 0589]
theorem subset_weaklyAssociatedPrimes {R : Type u} {M : Type v}
    [CommRing R] [AddCommGroup M] [Module R M] :
    associatedPrimesOfModule R M ⊆ weaklyAssociatedPrimes R M := sorry

end associatedPrimesOfModule

namespace associatedPrimes

/-- Associated primes are weakly associated. -/
@[stacks 0589]
theorem subset_weaklyAssociatedPrimes {R : Type u} {M : Type v}
    [CommRing R] [AddCommGroup M] [Module R M] :
    associatedPrimes R M ⊆ weaklyAssociatedPrimes R M := sorry

end associatedPrimes

namespace weaklyAssociatedPrimes

/-- Weakly associated primes lie in module support. -/
@[stacks 0589]
theorem subset_support {R : Type u} {M : Type v}
    [CommRing R] [AddCommGroup M] [Module R M] :
    PrimeSpectrum.asIdeal ⁻¹' weaklyAssociatedPrimes R M ⊆ Module.support R M := sorry

end weaklyAssociatedPrimes
