/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
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
    𝔭.IsPrime := by
  obtain ⟨m, hm⟩ := h𝔭
  exact hm.isPrime

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
    𝔭 ∈ weaklyAssociatedPrimes R M ↔ Ideal.IsWeaklyAssociatedToModule R M 𝔭 :=
  Iff.rfl

namespace weaklyAssociatedPrimes

/-- An element of the weakly associated-prime set carries its primality instance. -/
instance instIsPrime {R : Type u} {M : Type v}
    [CommRing R] [AddCommGroup M] [Module R M]
    (𝔭 : weaklyAssociatedPrimes R M) :
    𝔭.1.IsPrime :=
  𝔭.2.isPrime

/-- The weakly associated-prime set of a subsingleton module is empty. -/
theorem eq_empty_of_subsingleton {R : Type u} {M : Type v}
    [CommRing R] [AddCommGroup M] [Module R M] [Subsingleton M] :
    weaklyAssociatedPrimes R M = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro 𝔭 ⟨m, hm⟩
  simpa [Subsingleton.elim m 0, Ideal.torsionOf_zero, Ideal.minimalPrimes_top] using hm

/-- A nontrivial module has a weakly associated prime. -/
theorem nonempty {R : Type u} {M : Type v}
    [CommRing R] [AddCommGroup M] [Module R M] [Nontrivial M] :
    (weaklyAssociatedPrimes R M).Nonempty := by
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  obtain ⟨𝔭, h𝔭⟩ := Ideal.nonempty_minimalPrimes
    (I := Ideal.torsionOf R M m) (fun h ↦ hm ((Ideal.torsionOf_eq_top_iff R m).mp h))
  exact ⟨𝔭, m, h𝔭⟩

/-- The weakly associated-prime set is empty exactly when the module is subsingleton. -/
@[stacks 0588 "empty weakly associated-prime set"]
theorem eq_empty_iff_subsingleton {R : Type u} {M : Type v}
    [CommRing R] [AddCommGroup M] [Module R M] :
    weaklyAssociatedPrimes R M = ∅ ↔ Subsingleton M := by
  constructor
  · intro h
    by_contra hM
    letI : Nontrivial M := not_subsingleton_iff_nontrivial.mp hM
    obtain ⟨𝔭, h𝔭⟩ := nonempty (R := R) (M := M)
    simpa only [h, Set.notMem_empty] using h𝔭
  · intro hM
    letI := hM
    exact eq_empty_of_subsingleton

/-- Weakly associated primes commute with restriction of scalars along a quotient map. -/
@[stacks 05C8]
theorem image_comap_quotient_eq {R : Type u} [CommRing R]
    (I : Ideal R) {M : Type v} [AddCommGroup M] [Module (R ⧸ I) M] [Module R M]
    [IsScalarTower R (R ⧸ I) M] :
    Ideal.comap (algebraMap R (R ⧸ I)) '' weaklyAssociatedPrimes (R ⧸ I) M =
      weaklyAssociatedPrimes R M := by
  have hAnn (m : M) :
      (Ideal.torsionOf (R ⧸ I) M m).comap (algebraMap R (R ⧸ I)) =
        Ideal.torsionOf R M m := by
    ext r
    rw [Ideal.mem_comap, Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff,
      IsScalarTower.algebraMap_smul (R ⧸ I)]
  have hsurj : Function.Surjective (algebraMap R (R ⧸ I)) :=
    Ideal.Quotient.mk_surjective
  ext 𝔭
  constructor
  · rintro ⟨𝔮, ⟨m, hm⟩, rfl⟩
    refine ⟨m, ?_⟩
    rw [← hAnn m]
    exact Ideal.minimalPrimes_comap_of_surjective hsurj hm
  · rintro ⟨m, hm⟩
    rw [← hAnn m, Ideal.comap_minimalPrimes_eq_of_surjective hsurj] at hm
    obtain ⟨𝔮, h𝔮, h𝔮𝔭⟩ := hm
    exact ⟨𝔮, ⟨m, h𝔮⟩, h𝔮𝔭⟩

/-- Over a reduced ring, the weakly associated primes of the regular module are exactly the
minimal primes. -/
@[stacks 0EMA]
theorem ring_eq_minimalPrimes {R : Type u} [CommRing R] [IsReduced R] :
    weaklyAssociatedPrimes R R = minimalPrimes R := by
  ext 𝔭
  constructor
  · rintro ⟨m, hm⟩
    have hmp : m ∉ 𝔭 := by
      intro hmp
      obtain ⟨y, hy, hmy⟩ := Ideal.exists_mul_mem_of_mem_minimalPrimes hm hmp
      apply hy
      rw [Ideal.mem_torsionOf_iff] at hmy ⊢
      change (m * y) * m = 0 at hmy
      change y * m = 0
      apply isNilpotent_iff_eq_zero.mp
      refine ⟨2, ?_⟩
      calc
        (y * m) ^ 2 = y * ((m * y) * m) := by rw [pow_two]; ac_rfl
        _ = 0 := by rw [hmy, mul_zero]
    refine ⟨⟨hm.isPrime, bot_le⟩, ?_⟩
    intro 𝔮 h𝔮 h𝔮𝔭
    apply hm.2 ⟨h𝔮.1, ?_⟩ h𝔮𝔭
    intro r hr
    have hrm : r * m = 0 := (Ideal.mem_torsionOf_iff m r).mp hr
    exact (h𝔮.1.mem_or_mem (hrm ▸ 𝔮.zero_mem)).resolve_right (fun h ↦ hmp (h𝔮𝔭 h))
  · intro h𝔭
    refine ⟨1, ?_⟩
    have hAnn : Ideal.torsionOf R R (1 : R) = ⊥ := by
      ext r
      simp [Ideal.mem_torsionOf_iff]
    rwa [hAnn]

/-- A minimal point of a module's support is weakly associated to that module. -/
@[stacks 05C4]
theorem mem_of_minimal_support {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (p : PrimeSpectrum R) (hp : Minimal (· ∈ Module.support R M) p) :
    p.asIdeal ∈ weaklyAssociatedPrimes R M := by
  obtain ⟨m, hm⟩ := Module.mem_support_iff_exists_annihilator.mp hp.1
  rw [Ideal.annihilator_span_singleton_eq_torsionOf] at hm
  refine ⟨m, ⟨⟨p.isPrime, hm⟩, ?_⟩⟩
  intro q hq hqp
  have hqs : (⟨q, hq.1⟩ : PrimeSpectrum R) ∈ Module.support R M :=
    Module.mem_support_iff_exists_annihilator.mpr
      ⟨m, (Ideal.annihilator_span_singleton_eq_torsionOf m).le.trans hq.2⟩
  exact hp.2 hqs hqp

end weaklyAssociatedPrimes

namespace LinearEquiv

/-- A linear equivalence identifies the weakly associated-prime sets of its source and target. -/
theorem weaklyAssociatedPrimes_eq
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    {N' : Type*} [AddCommGroup N'] [Module A N']
    (e : N ≃ₗ[A] N') :
    weaklyAssociatedPrimes A N = weaklyAssociatedPrimes A N' := by
  ext 𝔭
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨e m, ?_⟩
    change 𝔭 ∈ (Ideal.torsionOf A N' (e.toLinearMap m)).minimalPrimes
    rwa [Ideal.torsionOf_map_eq_of_injective (f := e.toLinearMap) e.injective m]
  · rintro ⟨m, hm⟩
    refine ⟨e.symm m, ?_⟩
    change 𝔭 ∈ (Ideal.torsionOf A N (e.symm.toLinearMap m)).minimalPrimes
    rwa [Ideal.torsionOf_map_eq_of_injective (f := e.symm.toLinearMap) e.symm.injective m]

end LinearEquiv

namespace IsAssociatedPrime

/-- A radical-based associated prime is weakly associated to the same module. -/
theorem isWeaklyAssociatedToModule {R : Type u} {M : Type v}
    [CommRing R] [AddCommGroup M] [Module R M] {𝔭 : Ideal R}
    (h𝔭 : IsAssociatedPrime 𝔭 M) :
    Ideal.IsWeaklyAssociatedToModule R M 𝔭 := by
  rcases h𝔭 with ⟨hPrime, m, hm⟩
  refine ⟨m, ⟨⟨hPrime, ?_⟩, ?_⟩⟩
  · rw [← Ideal.colon_bot_singleton_eq_torsionOf R M m, hm]
    exact Ideal.le_radical
  · intro q hq hqp
    rw [hm, Ideal.colon_bot_singleton_eq_torsionOf R M m]
    exact hq.1.radical_le_iff.mpr hq.2

end IsAssociatedPrime

namespace Ideal

/-- An exact-annihilator associated prime is weakly associated to the same module. -/
theorem IsAssociatedToModule.isWeaklyAssociatedToModule {R : Type u} {M : Type v}
    [CommRing R] [AddCommGroup M] [Module R M] {𝔭 : Ideal R}
    (h𝔭 : IsAssociatedToModule R M 𝔭) :
    IsWeaklyAssociatedToModule R M 𝔭 :=
  h𝔭.isAssociatedPrime.isWeaklyAssociatedToModule

/-- A weakly associated prime, viewed as a point of `Spec R`, belongs to the module support. -/
theorem IsWeaklyAssociatedToModule.mem_support {R : Type u} {M : Type v}
    [CommRing R] [AddCommGroup M] [Module R M] {𝔭 : Ideal R}
    (h𝔭 : IsWeaklyAssociatedToModule R M 𝔭) :
    (⟨𝔭, h𝔭.isPrime⟩ : PrimeSpectrum R) ∈ Module.support R M := by
  obtain ⟨m, hm⟩ := h𝔭
  exact Module.mem_support_iff_exists_annihilator.mpr
    ⟨m, (annihilator_span_singleton_eq_torsionOf m).le.trans hm.le⟩

end Ideal

namespace associatedPrimesOfModule

/-- Exact-annihilator associated primes are weakly associated. -/
@[stacks 0589]
theorem subset_weaklyAssociatedPrimes {R : Type u} {M : Type v}
    [CommRing R] [AddCommGroup M] [Module R M] :
    associatedPrimesOfModule R M ⊆ weaklyAssociatedPrimes R M := by
  intro 𝔭 h𝔭
  exact Ideal.IsAssociatedToModule.isWeaklyAssociatedToModule h𝔭

end associatedPrimesOfModule

namespace associatedPrimes

/-- Associated primes are weakly associated. -/
@[stacks 0589]
theorem subset_weaklyAssociatedPrimes {R : Type u} {M : Type v}
    [CommRing R] [AddCommGroup M] [Module R M] :
    associatedPrimes R M ⊆ weaklyAssociatedPrimes R M := by
  intro 𝔭 h𝔭
  exact IsAssociatedPrime.isWeaklyAssociatedToModule h𝔭

end associatedPrimes

namespace weaklyAssociatedPrimes

/-- Weakly associated primes lie in module support. -/
@[stacks 0589]
theorem subset_support {R : Type u} {M : Type v}
    [CommRing R] [AddCommGroup M] [Module R M] :
    PrimeSpectrum.asIdeal ⁻¹' weaklyAssociatedPrimes R M ⊆ Module.support R M := by
  intro 𝔭 h𝔭
  exact Ideal.IsWeaklyAssociatedToModule.mem_support h𝔭

end weaklyAssociatedPrimes
