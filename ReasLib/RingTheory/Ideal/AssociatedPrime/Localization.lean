/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Module
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Restriction
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open IsLocalRing

/-!
# Exact associated primes over localizations
-/

universe u v w

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable {M : Type w} [AddCommGroup M] [Module A M] [Module R M]
variable [IsScalarTower R A M]

/-- Exact associated primes of a module over a localization, contracted to the
base ring, are exactly the exact associated primes after restriction of scalars. -/
@[stacks 05BZ]
theorem associatedPrimesOfModule_image_comap_eq_of_isLocalization (T : Submonoid R)
    [IsLocalization T A] :
    Ideal.comap (algebraMap R A) '' associatedPrimesOfModule A M =
      associatedPrimesOfModule R M := by
  refine Set.Subset.antisymm (associatedPrimesOfModule.Restriction.image_comap_subset R M) ?_
  rintro p ⟨hp, m, hm⟩
  have hcomap : (Ideal.torsionOf A M m).under R = p := by
    ext r
    rw [Ideal.mem_comap, Ideal.mem_torsionOf_iff, IsScalarTower.algebraMap_smul,
      hm, Ideal.mem_torsionOf_iff]
  have hne : Ideal.torsionOf A M m ≠ ⊤ := by
    intro htop
    apply hp.ne_top
    rw [← hcomap, htop]
    rfl
  have hprime : (Ideal.torsionOf A M m).IsPrime :=
    (IsLocalization.isPrime_iff_isPrime_disjoint T A _).mpr
      ⟨hcomap.symm ▸ hp, (IsLocalization.disjoint_under_iff T A _).mpr hne⟩
  exact ⟨Ideal.torsionOf A M m, ⟨hprime, m, rfl⟩, hcomap⟩

end

section

variable {R : Type u} [CommRing R]
variable (T : Submonoid R)
variable {M : Type v} [AddCommGroup M] [Module R M]

private theorem associatedToModule_localizedModule_of_disjoint {p : Ideal R}
    (hp : Ideal.IsAssociatedToModule R M p)
    (hT : Disjoint (T : Set R) (p : Set R)) :
    Ideal.IsAssociatedToModule R (LocalizedModule T M) p := by
  rcases hp with ⟨hp, m, hm⟩
  refine ⟨hp, LocalizedModule.mkLinearMap T M m, ?_⟩
  ext r
  rw [Ideal.mem_torsionOf_iff]
  constructor
  · intro hr
    have hrm : r • m = 0 := by
      simpa only [hm, Ideal.mem_torsionOf_iff] using hr
    simpa using congrArg (LocalizedModule.mkLinearMap T M) hrm
  · intro hr
    have hz : LocalizedModule.mkLinearMap T M (r • m) = 0 := by
      simpa using hr
    obtain ⟨s, hs⟩ :=
      (IsLocalizedModule.eq_zero_iff T (LocalizedModule.mkLinearMap T M)).mp hz
    have hsr : (s : R) * r ∈ p := by
      rw [hm, Ideal.mem_torsionOf_iff, mul_smul]
      exact hs
    exact (hp.mem_or_mem hsr).resolve_left (Set.disjoint_left.mp hT s.property)

private theorem associatedToModule_of_localizedModule_of_fg {p : Ideal R}
    (hp : Ideal.IsAssociatedToModule R (LocalizedModule T M) p) (hfg : p.FG) :
    Ideal.IsAssociatedToModule R M p := by
  classical
  let f := LocalizedModule.mkLinearMap T M
  rcases hp with ⟨hp, x, hx⟩
  obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective T f x
  simp only [Function.uncurry_apply_pair] at hx
  have hm : p = Ideal.torsionOf R (LocalizedModule T M) (f m) := by
    ext r
    simp only [hx, Ideal.mem_torsionOf_iff, ← IsLocalizedModule.mk'_smul,
      IsLocalizedModule.mk'_eq_zero, map_smul]
  rcases hfg with ⟨F, hF⟩
  have mem (a : F) : ∃ t : T, t • ((a : R) • m) = 0 := by
    apply (IsLocalizedModule.eq_zero_iff T f).mp
    rw [map_smul, ← Ideal.mem_torsionOf_iff, ← hm, ← hF]
    exact Ideal.subset_span a.property
  choose g hg using mem
  let t : T := ∏ a : F, g a
  refine ⟨hp, (t : R) • m, le_antisymm ?_ ?_⟩
  · rw [← hF, Ideal.span_le]
    intro a ha
    obtain ⟨u, hu⟩ : g ⟨a, ha⟩ ∣ t :=
      Finset.dvd_prod_of_mem g (Finset.mem_univ (⟨a, ha⟩ : F))
    change a • ((t : R) • m) = 0
    calc
      a • (t : R) • m = (u : R) • ((g ⟨a, ha⟩ : R) • (a • m)) := by
        rw [hu, Submonoid.coe_mul, smul_comm a, mul_smul,
          smul_comm (g ⟨a, ha⟩ : R) (u : R)]
      _ = 0 := by
        rw [show (g ⟨a, ha⟩ : R) • (a • m) = 0 from hg ⟨a, ha⟩, smul_zero]
  · intro r hr
    rw [hm, Ideal.mem_torsionOf_iff]
    apply IsLocalizedModule.smul_injective f t
    change (t : R) • (r • f m) = (t : R) • 0
    rw [smul_zero, smul_comm (t : R) r, ← map_smul, ← map_smul,
      show r • ((t : R) • m) = 0 from hr, map_zero]

/-- The exact associated primes of a localized module agree with the contractions of its exact
associated primes over the localization. -/
@[stacks 05BZ]
theorem associatedPrimesOfModule_localizedModule_eq_image_comap :
    Ideal.comap (algebraMap R (Localization T)) ''
        associatedPrimesOfModule (Localization T) (LocalizedModule T M) =
      associatedPrimesOfModule R (LocalizedModule T M) :=
  associatedPrimesOfModule_image_comap_eq_of_isLocalization T

end

namespace Ideal.IsAssociatedToModule.Localization

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Exact association at a prime ascends to exact association of the maximal ideal after
localization at that prime. -/
@[stacks 0310 "exact associated prime ascends to the local maximal ideal"]
theorem maximalIdeal_atPrime {p : Ideal R} [p.IsPrime]
    (hp : Ideal.IsAssociatedToModule R M p) :
    Ideal.IsAssociatedToModule (Localization.AtPrime p) (LocalizedModule.AtPrime p M)
      (maximalIdeal (Localization.AtPrime p)) := by
  have hloc := associatedToModule_localizedModule_of_disjoint p.primeCompl hp
    disjoint_compl_left
  change p ∈ associatedPrimesOfModule R (LocalizedModule.AtPrime p M) at hloc
  rw [← associatedPrimesOfModule_localizedModule_eq_image_comap] at hloc
  obtain ⟨P, hP, hcomap⟩ := hloc
  have hPmax : P = maximalIdeal (Localization.AtPrime p) :=
    Localization.AtPrime.eq_maximalIdeal_iff_under_eq.mp hcomap
  exact hPmax ▸ hP

/-- Exact association of the local maximal ideal descends along localization when the original
prime is finitely generated. -/
@[stacks 0310 "finitely generated local maximal ideal descends"]
theorem of_maximalIdeal_atPrime {p : Ideal R} [p.IsPrime]
    (hp :
      Ideal.IsAssociatedToModule (Localization.AtPrime p) (LocalizedModule.AtPrime p M)
        (maximalIdeal (Localization.AtPrime p)))
    (hfg : p.FG) :
    Ideal.IsAssociatedToModule R M p := by
  have hcomap := Ideal.isAssociatedToModule_comap R (LocalizedModule.AtPrime p M) hp
  rw [show Ideal.comap (algebraMap R (Localization.AtPrime p))
      (maximalIdeal (Localization.AtPrime p)) = p from
    Localization.AtPrime.under_maximalIdeal] at hcomap
  exact associatedToModule_of_localizedModule_of_fg p.primeCompl hcomap hfg

/-- For a finitely generated prime, exact association is equivalent to exact association of the
maximal ideal after localization at that prime. -/
@[stacks 0310 "localization criterion for finitely generated exact associated primes"]
theorem iff_maximalIdeal_atPrime {p : Ideal R} [p.IsPrime] (hfg : p.FG) :
    Ideal.IsAssociatedToModule R M p ↔
      Ideal.IsAssociatedToModule (Localization.AtPrime p) (LocalizedModule.AtPrime p M)
        (maximalIdeal (Localization.AtPrime p)) :=
  ⟨maximalIdeal_atPrime, fun hp ↦ of_maximalIdeal_atPrime hp hfg⟩

variable (T : Submonoid R)

/-- If every denominator acts regularly, exact association of a fixed prime is unchanged when the
module is localized and then viewed over the base ring. -/
@[stacks 05C0 "pointwise exact association under localization by regular elements"]
theorem iff_of_isSMulRegular {p : Ideal R}
    (hT : ∀ t : T, IsSMulRegular M t) :
    Ideal.IsAssociatedToModule R M p ↔
      Ideal.IsAssociatedToModule R (LocalizedModule T M) p := by
  let f := LocalizedModule.mkLinearMap T M
  have hf : Function.Injective f := (IsLocalizedModule.injective_iff_isRegular T f).mpr hT
  constructor
  · intro hp
    exact Ideal.isAssociatedToModule_map_of_injective R M hp f hf
  · rintro ⟨hp, x, hx⟩
    obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective T f x
    simp only [Function.uncurry_apply_pair] at hx
    refine ⟨hp, m, ?_⟩
    ext r
    rw [hx, Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff,
      ← IsLocalizedModule.mk'_smul, IsLocalizedModule.mk'_eq_zero]
    exact ⟨fun h ↦ hf (by simpa using h), fun h ↦ by simp [h]⟩

end Ideal.IsAssociatedToModule.Localization

namespace associatedPrimesOfModule.Localization

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Membership in the exact associated-prime set ascends to membership of the local maximal ideal
after localization at that prime. -/
@[stacks 0310 "exact associated-prime membership ascends to the local maximal ideal"]
theorem maximalIdeal_mem_atPrime {p : Ideal R} [p.IsPrime]
    (hp : p ∈ associatedPrimesOfModule R M) :
    maximalIdeal (Localization.AtPrime p) ∈
      associatedPrimesOfModule (Localization.AtPrime p) (LocalizedModule.AtPrime p M) :=
  Ideal.IsAssociatedToModule.Localization.maximalIdeal_atPrime hp

/-- Membership of the local maximal ideal descends to a finitely generated exact associated
prime. -/
@[stacks 0310 "local maximal-ideal membership descends to a finitely generated prime"]
theorem mem_of_maximalIdeal_mem_atPrime {p : Ideal R} [p.IsPrime]
    (hp :
      maximalIdeal (Localization.AtPrime p) ∈
        associatedPrimesOfModule (Localization.AtPrime p) (LocalizedModule.AtPrime p M))
    (hfg : p.FG) :
    p ∈ associatedPrimesOfModule R M :=
  Ideal.IsAssociatedToModule.Localization.of_maximalIdeal_atPrime hp hfg

/-- For a finitely generated prime, membership in the exact associated-prime set is detected by
the maximal ideal after localization at that prime. -/
@[stacks 0310 "set-level localization criterion for finitely generated exact associated primes"]
theorem mem_iff_maximalIdeal_mem_atPrime {p : Ideal R} [p.IsPrime] (hfg : p.FG) :
    p ∈ associatedPrimesOfModule R M ↔
      maximalIdeal (Localization.AtPrime p) ∈
        associatedPrimesOfModule (Localization.AtPrime p) (LocalizedModule.AtPrime p M) :=
  Ideal.IsAssociatedToModule.Localization.iff_maximalIdeal_atPrime hfg

variable (T : Submonoid R)

/-- An exact associated prime disjoint from the denominator submonoid remains exact associated
after localization, with the localized module viewed over the base ring. -/
@[stacks 05BZ "pointwise persistence of a disjoint exact associated prime"]
theorem mem_localizedModule {p : Ideal R}
    (hp : p ∈ associatedPrimesOfModule R M)
    (hT : Disjoint (T : Set R) (p : Set R)) :
    p ∈ associatedPrimesOfModule R (LocalizedModule T M) :=
  associatedToModule_localizedModule_of_disjoint T hp hT

/-- Exact associated primes disjoint from a submonoid remain exact associated primes after
localization, with the localized module viewed over the base ring. -/
@[stacks 05BZ "disjoint exact associated primes persist under localization"]
theorem inter_disjoint_subset :
    associatedPrimesOfModule R M ∩
        { p : Ideal R | Disjoint (T : Set R) (p : Set R) } ⊆
      associatedPrimesOfModule R (LocalizedModule T M) := by
  rintro p ⟨hp, hT⟩
  exact mem_localizedModule T hp hT

/-- Range formulation of persistence of exact associated primes under localization. -/
@[stacks 05BZ "range form of exact associated-prime persistence"]
theorem inter_range_subset :
    associatedPrimesOfModule R M ∩
        Set.range (Ideal.comap (algebraMap R (Localization T))) ⊆
      associatedPrimesOfModule R (LocalizedModule T M) := by
  rintro p ⟨hp, P, rfl⟩
  apply mem_localizedModule T hp
  apply (IsLocalization.disjoint_under_iff T (Localization T) P).mpr
  intro htop
  exact hp.1.ne_top (by rw [htop, Ideal.comap_top])

/-- Over a Noetherian ring, exact associated primes of a localized module are exactly the exact
associated primes of the original module disjoint from the localization submonoid. -/
@[stacks 05BZ "Noetherian exact associated primes under localization"]
theorem inter_disjoint_eq [IsNoetherianRing R] :
    associatedPrimesOfModule R M ∩
        { p : Ideal R | Disjoint (T : Set R) (p : Set R) } =
      associatedPrimesOfModule R (LocalizedModule T M) := by
  refine Set.Subset.antisymm (inter_disjoint_subset T) ?_
  intro p hp
  refine ⟨associatedToModule_of_localizedModule_of_fg T hp p.fg_of_isNoetherianRing, ?_⟩
  rw [← associatedPrimesOfModule_localizedModule_eq_image_comap] at hp
  obtain ⟨P, hP, rfl⟩ := hp
  exact (IsLocalization.disjoint_under_iff T (Localization T) P).mpr hP.1.ne_top

/-- Range formulation of the Noetherian exact associated-prime localization equality. -/
@[stacks 05BZ "range form of Noetherian exact associated-prime localization"]
theorem inter_range_eq [IsNoetherianRing R] :
    associatedPrimesOfModule R M ∩
        Set.range (Ideal.comap (algebraMap R (Localization T))) =
      associatedPrimesOfModule R (LocalizedModule T M) := by
  refine Set.Subset.antisymm (inter_range_subset T) ?_
  intro p hp
  refine ⟨associatedToModule_of_localizedModule_of_fg T hp p.fg_of_isNoetherianRing, ?_⟩
  rw [← associatedPrimesOfModule_localizedModule_eq_image_comap] at hp
  obtain ⟨P, _, hP⟩ := hp
  exact ⟨P, hP⟩

/-- Over a Noetherian ring, a prime is exact associated to the localized module exactly when it
was exact associated before localization and is disjoint from the denominator submonoid. -/
@[stacks 05BZ "pointwise Noetherian exact associated-prime localization criterion"]
theorem mem_localizedModule_iff [IsNoetherianRing R] {p : Ideal R} :
    p ∈ associatedPrimesOfModule R (LocalizedModule T M) ↔
      p ∈ associatedPrimesOfModule R M ∧
        Disjoint (T : Set R) (p : Set R) := by
  rw [← inter_disjoint_eq T]
  rfl

/-- If every denominator acts regularly, exact association is unchanged when the module is
localized and then viewed over the base ring. -/
@[stacks 05C0 "pointwise exact association under localization by regular elements"]
theorem mem_iff_of_isSMulRegular {p : Ideal R}
    (hT : ∀ t : T, IsSMulRegular M t) :
    p ∈ associatedPrimesOfModule R M ↔
      p ∈ associatedPrimesOfModule R (LocalizedModule T M) :=
  Ideal.IsAssociatedToModule.Localization.iff_of_isSMulRegular T hT

/-- If every denominator acts regularly, localization does not change the exact associated-prime
set when the localized module is viewed over the base ring. -/
@[stacks 05C0 "exact associated primes under localization by regular elements"]
theorem eq_of_isSMulRegular (hT : ∀ t : T, IsSMulRegular M t) :
    associatedPrimesOfModule R M =
      associatedPrimesOfModule R (LocalizedModule T M) := by
  ext p
  exact mem_iff_of_isSMulRegular T hT

end associatedPrimesOfModule.Localization

namespace associatedPrimes.Localization

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable (T : Submonoid R)

/-- Over a Noetherian ring, associated primes of a localized module are exactly the associated
primes of the original module disjoint from the localization submonoid. -/
@[stacks 05BZ "Noetherian associated primes under localization"]
theorem inter_disjoint_eq [IsNoetherianRing R] :
    associatedPrimes R M ∩
        { p : Ideal R | Disjoint (T : Set R) (p : Set R) } =
      associatedPrimes R (LocalizedModule T M) := by
  simpa only [← associatedPrimesOfModule_eq_associatedPrimes] using
    associatedPrimesOfModule.Localization.inter_disjoint_eq (M := M) T

/-- Range formulation of the Noetherian associated-prime localization equality. -/
@[stacks 05BZ "range form of Noetherian associated-prime localization"]
theorem inter_range_eq [IsNoetherianRing R] :
    associatedPrimes R M ∩
        Set.range (Ideal.comap (algebraMap R (Localization T))) =
      associatedPrimes R (LocalizedModule T M) := by
  simpa only [← associatedPrimesOfModule_eq_associatedPrimes] using
    associatedPrimesOfModule.Localization.inter_range_eq (M := M) T

/-- Over a Noetherian ring, membership in the associated-prime set after localization is
equivalent to original membership together with disjointness from the denominators. -/
@[stacks 05BZ "pointwise Noetherian associated-prime localization criterion"]
theorem mem_localizedModule_iff [IsNoetherianRing R] {p : Ideal R} :
    p ∈ associatedPrimes R (LocalizedModule T M) ↔
      p ∈ associatedPrimes R M ∧ Disjoint (T : Set R) (p : Set R) := by
  rw [← inter_disjoint_eq T]
  rfl

/-- If every denominator acts regularly, localization does not change the associated-prime set
when the localized module is viewed over a Noetherian base ring. -/
@[stacks 05C0 "associated primes under localization by regular elements"]
theorem eq_of_isSMulRegular [IsNoetherianRing R]
    (hT : ∀ t : T, IsSMulRegular M t) :
    associatedPrimes R M =
      associatedPrimes R (LocalizedModule T M) := by
  simpa only [← associatedPrimesOfModule_eq_associatedPrimes] using
    associatedPrimesOfModule.Localization.eq_of_isSMulRegular (M := M) T hT

end associatedPrimes.Localization
