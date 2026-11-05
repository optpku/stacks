module

public import ReasLib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Support
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Exact Associated Primes of Modules

This module owns the exact-annihilator variant of associated primes.  Mathlib's
`IsAssociatedPrime` uses the radical of an annihilator, whereas exact association
records an element whose annihilator is the prime ideal itself.  The
comparison and functoriality API below lets downstream users work at either level.
-/

universe u v

section

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

namespace Ideal

/-- A prime ideal `𝔭` of `R` is exactly associated to the `R`-module `M` when it is the
annihilator ideal of an element of `M`. -/
@[stacks 00LA]
def IsAssociatedToModule (𝔭 : Ideal R) : Prop :=
  𝔭.IsPrime ∧ ∃ m : M, 𝔭 = torsionOf R M m

/-- The annihilator-colon presentation used by Mathlib agrees with the elementwise torsion
ideal presentation. -/
@[simp]
theorem colon_bot_singleton_eq_torsionOf (m : M) :
    (⊥ : Submodule R M).colon {m} = torsionOf R M m := by
  ext r
  simp [Submodule.mem_colon_singleton]

/-- An injective linear map carries an exact-annihilator associated prime to the target module. -/
theorem isAssociatedToModule_map_of_injective {M' : Type*} [AddCommGroup M'] [Module R M']
    {𝔭 : Ideal R} (h𝔭 : IsAssociatedToModule R M 𝔭) (f : M →ₗ[R] M')
    (hf : Function.Injective f) :
    IsAssociatedToModule R M' 𝔭 := by
  rcases h𝔭 with ⟨h𝔭Prime, m, hm⟩
  refine ⟨h𝔭Prime, f m, ?_⟩
  rw [torsionOf_map_eq_of_injective hf]
  exact hm

/-- Exact association is equivalently witnessed by a prime ideal equal to an element torsion
ideal.  This exposes the computation-friendly formulation of the definition. -/
theorem isAssociatedToModule_iff_exists_torsionOf (𝔭 : Ideal R) :
    IsAssociatedToModule R M 𝔭 ↔ 𝔭.IsPrime ∧ ∃ m : M, 𝔭 = torsionOf R M m :=
  Iff.rfl

/-- An exact-annihilator associated prime is associated in mathlib's radical-based sense. -/
theorem IsAssociatedToModule.isAssociatedPrime {𝔭 : Ideal R}
    (h𝔭 : IsAssociatedToModule R M 𝔭) :
    IsAssociatedPrime 𝔭 M := by
  rcases h𝔭 with ⟨h𝔭Prime, m, hm⟩
  refine ⟨h𝔭Prime, m, ?_⟩
  rw [colon_bot_singleton_eq_torsionOf, ← hm]
  exact h𝔭Prime.radical.symm

/-- Restricting scalars along `R → S` contracts an exact-annihilator associated prime. -/
theorem isAssociatedToModule_comap {S : Type*} [CommRing S] [Algebra R S]
    [Module S M] [IsScalarTower R S M] {P : Ideal S} (hP : IsAssociatedToModule S M P) :
    IsAssociatedToModule R M (Ideal.comap (algebraMap R S) P) := by
  rcases hP with ⟨hPPrime, m, hm⟩
  refine ⟨hPPrime.comap (algebraMap R S), m, ?_⟩
  ext r
  rw [Ideal.mem_comap, hm, mem_torsionOf_iff, mem_torsionOf_iff,
    IsScalarTower.algebraMap_smul S]

/-- Over a Noetherian ring, exact-annihilator association agrees with mathlib's associated-prime
predicate. -/
theorem isAssociatedToModule_iff_isAssociatedPrime [IsNoetherianRing R] (𝔭 : Ideal R) :
    IsAssociatedToModule R M 𝔭 ↔ IsAssociatedPrime 𝔭 M := by
  simpa [IsAssociatedToModule, colon_bot_singleton_eq_torsionOf] using
    (isAssociatedPrime_iff (I := 𝔭) (M := M)).symm

end Ideal

namespace LinearEquiv

/-- Exact-annihilator association is invariant under a linear equivalence of modules. -/
theorem isAssociatedToModule_iff {M' : Type*} [AddCommGroup M'] [Module R M']
    (e : M ≃ₗ[R] M') {𝔭 : Ideal R} :
    Ideal.IsAssociatedToModule R M 𝔭 ↔ Ideal.IsAssociatedToModule R M' 𝔭 :=
  ⟨fun h ↦ Ideal.isAssociatedToModule_map_of_injective R M h e e.injective,
    fun h ↦ Ideal.isAssociatedToModule_map_of_injective R M' h e.symm e.symm.injective⟩

end LinearEquiv

/-- The set of exact-annihilator associated primes of the `R`-module `M`. -/
@[stacks 00LA "exact associated-prime set"]
def associatedPrimesOfModule : Set (Ideal R) :=
  { 𝔭 | Ideal.IsAssociatedToModule R M 𝔭 }

/-- Membership in `associatedPrimesOfModule` is exact-annihilator association. -/
@[simp, stacks 00LA "exact associated-prime membership"]
theorem mem_associatedPrimesOfModule_iff (𝔭 : Ideal R) :
    𝔭 ∈ associatedPrimesOfModule R M ↔ Ideal.IsAssociatedToModule R M 𝔭 :=
  Iff.rfl

namespace LinearEquiv

/-- A linear equivalence identifies the exact-annihilator associated-prime sets of its source and
target. -/
theorem associatedPrimesOfModule_eq {M' : Type*} [AddCommGroup M'] [Module R M']
    (e : M ≃ₗ[R] M') :
    associatedPrimesOfModule R M = associatedPrimesOfModule R M' := by
  ext 𝔭
  exact e.isAssociatedToModule_iff

end LinearEquiv

/-- Exact-annihilator associated primes are contained in mathlib's radical-based associated-prime
set. -/
@[stacks 00LA "exact associated primes are associated"]
theorem associatedPrimesOfModule_subset_associatedPrimes :
    associatedPrimesOfModule R M ⊆ associatedPrimes R M := by
  intro 𝔭 h𝔭
  exact h𝔭.isAssociatedPrime

namespace associatedPrimesOfModule.Restriction

/-- Contracting exact associated primes along a scalar tower produces exact associated primes
after restricting scalars. -/
@[stacks 05BW]
theorem image_comap_subset
    {S : Type*} [CommRing S] [Algebra R S] [Module S M] [IsScalarTower R S M] :
    Ideal.comap (algebraMap R S) '' associatedPrimesOfModule S M ⊆
      associatedPrimesOfModule R M := by
  rintro 𝔭 ⟨P, hP, rfl⟩
  exact Ideal.isAssociatedToModule_comap R M hP

end associatedPrimesOfModule.Restriction

/-- Over a Noetherian ring, exact-annihilator and radical-based associated-prime sets coincide. -/
@[stacks 00LA "exact and radical associated primes over Noetherian rings"]
theorem associatedPrimesOfModule_eq_associatedPrimes [IsNoetherianRing R] :
    associatedPrimesOfModule R M = associatedPrimes R M := by
  ext 𝔭
  exact Ideal.isAssociatedToModule_iff_isAssociatedPrime R M 𝔭

namespace IsAssociatedPrime

/-- A radical-based associated prime, viewed as a point of `Spec R`, lies in the support of the
module. -/
@[stacks 0586 "associated prime points lie in support"]
theorem mem_support {𝔭 : Ideal R} (h𝔭 : IsAssociatedPrime 𝔭 M) :
    (⟨𝔭, h𝔭.isPrime⟩ : PrimeSpectrum R) ∈ Module.support R M := by
  rcases h𝔭 with ⟨h𝔭Prime, m, hm⟩
  refine Module.mem_support_iff_exists_annihilator.mpr ⟨m, ?_⟩
  calc
    (R ∙ m).annihilator = Ideal.torsionOf R M m :=
      Ideal.annihilator_span_singleton_eq_torsionOf m
    _ = (⊥ : Submodule R M).colon {m} :=
      (Ideal.colon_bot_singleton_eq_torsionOf R M m).symm
    _ ≤ ((⊥ : Submodule R M).colon {m}).radical := Ideal.le_radical
    _ = 𝔭 := hm.symm

end IsAssociatedPrime

namespace associatedPrimes

/-- All radical-based associated-prime points lie in module support. The preimage form keeps the
statement at the `PrimeSpectrum` owner and is directly consumable by set reasoning. -/
@[stacks 0586 "associated-prime set lies in support"]
theorem subset_support :
    PrimeSpectrum.asIdeal ⁻¹' associatedPrimes R M ⊆ Module.support R M := by
  intro 𝔭 h𝔭
  exact IsAssociatedPrime.mem_support R M (AssociatedPrimes.mem_iff.mp h𝔭)

end associatedPrimes

namespace associatedPrimesOfModule

/-- All exact-annihilator associated-prime points lie in module support. -/
@[stacks 0586 "exact associated-prime set lies in support"]
theorem subset_support :
    PrimeSpectrum.asIdeal ⁻¹' associatedPrimesOfModule R M ⊆ Module.support R M := by
  intro 𝔭 h𝔭
  exact associatedPrimes.subset_support R M
    (associatedPrimesOfModule_subset_associatedPrimes R M h𝔭)

end associatedPrimesOfModule

namespace Module

/-- The radical-based associated-prime set of a module lies in its support. -/
theorem associatedPrimes_subset_support :
    PrimeSpectrum.asIdeal ⁻¹' associatedPrimes R M ⊆ support R M :=
  associatedPrimes.subset_support R M

/-- The exact-annihilator associated-prime set of a module lies in its support. -/
theorem associatedPrimesOfModule_subset_support :
    PrimeSpectrum.asIdeal ⁻¹' associatedPrimesOfModule R M ⊆ support R M :=
  associatedPrimesOfModule.subset_support R M

end Module

end
