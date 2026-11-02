/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic
public import ReasLib.RingTheory.Module.Support.Minimal
public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Tactic.FinCases

/-!
# Localization of two-periodic complexes

This file constructs the localization of a two-periodic endomorphism complex at a prime and
records its behavior at a minimal point of the support.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism

variable {R : Type u} [CommRing R]

/-- The two localized differentials still compose to zero in degree zero. -/
theorem localizedAtPrime_d₀_d₁
    (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) (q : PrimeSpectrum R) :
    ModuleCat.ofHom (LocalizedModule.map q.asIdeal.primeCompl K.d₀.hom) ≫
      ModuleCat.ofHom (LocalizedModule.map q.asIdeal.primeCompl K.d₁.hom) = 0 := by
  apply ModuleCat.hom_ext
  change (LocalizedModule.map q.asIdeal.primeCompl K.d₁.hom).comp
      (LocalizedModule.map q.asIdeal.primeCompl K.d₀.hom) = 0
  apply LinearMap.ext
  intro x
  induction x using LocalizedModule.induction_on with
  | _ x s =>
    simp only [LocalizedModule.map_mk, LinearMap.comp_apply]
    have hcomp : K.d₁.hom.comp K.d₀.hom = 0 := by
      have h := congrArg ModuleCat.Hom.hom K.d₀_d₁
      simpa [ModuleCat.ofHom_comp] using h
    change LocalizedModule.mk ((K.d₁.hom.comp K.d₀.hom) x) s = 0
    rw [hcomp]
    simp

/-- The two localized differentials still compose to zero in degree one. -/
theorem localizedAtPrime_d₁_d₀
    (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) (q : PrimeSpectrum R) :
    ModuleCat.ofHom (LocalizedModule.map q.asIdeal.primeCompl K.d₁.hom) ≫
      ModuleCat.ofHom (LocalizedModule.map q.asIdeal.primeCompl K.d₀.hom) = 0 := by
  apply ModuleCat.hom_ext
  change (LocalizedModule.map q.asIdeal.primeCompl K.d₀.hom).comp
      (LocalizedModule.map q.asIdeal.primeCompl K.d₁.hom) = 0
  apply LinearMap.ext
  intro x
  induction x using LocalizedModule.induction_on with
  | _ x s =>
    simp only [LocalizedModule.map_mk, LinearMap.comp_apply]
    have hcomp : K.d₀.hom.comp K.d₁.hom = 0 := by
      have h := congrArg ModuleCat.Hom.hom K.d₁_d₀
      simpa [ModuleCat.ofHom_comp] using h
    change LocalizedModule.mk ((K.d₀.hom.comp K.d₁.hom) x) s = 0
    rw [hcomp]
    simp

/-- The two-periodic endomorphism complex obtained by localizing its module and differentials at
a prime ideal. -/
noncomputable def localizedAtPrime
    (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) (q : PrimeSpectrum R) :
    TwoPeriodicEndomorphism (ModuleCat.{max u v} (Localization.AtPrime q.asIdeal)) where
  X := ModuleCat.of (Localization.AtPrime q.asIdeal)
    (LocalizedModule.AtPrime q.asIdeal K.X)
  d₀ := ModuleCat.ofHom (LocalizedModule.map q.asIdeal.primeCompl K.d₀.hom)
  d₁ := ModuleCat.ofHom (LocalizedModule.map q.asIdeal.primeCompl K.d₁.hom)
  d₀_d₁ := localizedAtPrime_d₀_d₁ K q
  d₁_d₀ := localizedAtPrime_d₁_d₀ K q

/-- The carrier of `localizedAtPrime K q` is the localization of `K.X` at `q`. -/
theorem localizedAtPrime_X
    (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) (q : PrimeSpectrum R) :
    (localizedAtPrime K q).X = ModuleCat.of (Localization.AtPrime q.asIdeal)
      (LocalizedModule.AtPrime q.asIdeal K.X) := by
  rfl

/-- The degree-zero differential of `localizedAtPrime K q` is the localized map of `K.d₀`. -/
theorem localizedAtPrime_d₀
    (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) (q : PrimeSpectrum R) :
    (localizedAtPrime K q).d₀.hom =
      LocalizedModule.map q.asIdeal.primeCompl K.d₀.hom := by
  rfl

/-- The degree-one differential of `localizedAtPrime K q` is the localized map of `K.d₁`. -/
theorem localizedAtPrime_d₁
    (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) (q : PrimeSpectrum R) :
    (localizedAtPrime K q).d₁.hom =
      LocalizedModule.map q.asIdeal.primeCompl K.d₁.hom := by
  rfl

variable [IsLocalRing R] [IsNoetherianRing R]

/-- Localization at a minimal point of the support of a finite module has finite length over the
local ring at that point. -/
theorem localizedAtPrime_isFiniteLength
    (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) [Module.Finite R K.X]
    (q : PrimeSpectrum R) (hq : Minimal (· ∈ Module.support R K.X) q) :
    IsFiniteLength (Localization.AtPrime q.asIdeal) (localizedAtPrime K q).X := by
  exact Module.isFiniteLength_localizedAtPrime_of_minimalSupport K.X q hq

/-- If both cohomology modules have finite length and the support has dimension one, then the
localized two-periodic complex is acyclic at every minimal support point. -/
theorem localizedAtPrime_acyclic
    (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) [Module.Finite R K.X]
    (h₀ : IsFiniteLength R (K.toCochainComplex.homology 0))
    (h₁ : IsFiniteLength R (K.toCochainComplex.homology 1))
    (hdim : Module.supportDim R K.X = 1) (q : PrimeSpectrum R)
    (hq : Minimal (· ∈ Module.support R K.X) q) :
    (localizedAtPrime K q).toCochainComplex.Acyclic := by
  have hq_ne : q ≠ IsLocalRing.closedPoint R := by
    intro hqeq
    have heq : ∀ p, p ∈ Module.support R K.X → p = q := by
      intro p hp
      have hle : p ≤ q := by
        rw [hqeq]
        exact le_top
      exact le_antisymm hle (hq.2 hp hle)
    haveI : Subsingleton (Module.support R K.X) :=
      ⟨fun a b ↦ Subtype.ext ((heq _ a.2).trans (heq _ b.2).symm)⟩
    have hle := Order.krullDim_nonpos_of_subsingleton (α := Module.support R K.X)
    change Module.supportDim R K.X ≤ 0 at hle
    rw [hdim] at hle
    exact (not_le_of_gt (show (0 : WithBot ℕ∞) < 1 by norm_num)) hle
  -- Use the unshrunk localization, so no relation between the universes of R and K.X is needed.
  let F : ModuleCat.{v} R ⥤ ModuleCat.{max u v} (Localization.AtPrime q.asIdeal) :=
    { obj M := ModuleCat.of (Localization.AtPrime q.asIdeal)
        (LocalizedModule.AtPrime q.asIdeal M)
      map f := ModuleCat.ofHom (LocalizedModule.map q.asIdeal.primeCompl f.hom)
      map_id M := by
        ext x
        induction x using LocalizedModule.induction_on with
        | _ m s => simp
      map_comp f g := by
        ext x
        induction x using LocalizedModule.induction_on with
        | _ m s =>
          change (LocalizedModule.map q.asIdeal.primeCompl (g.hom.comp f.hom))
              (LocalizedModule.mk m s) =
            (LocalizedModule.map q.asIdeal.primeCompl g.hom)
              ((LocalizedModule.map q.asIdeal.primeCompl f.hom) (LocalizedModule.mk m s))
          simp }
  haveI : F.PreservesZeroMorphisms := by
    constructor
    intro M N
    apply ModuleCat.hom_ext
    change LocalizedModule.map q.asIdeal.primeCompl (0 : M →ₗ[R] N) = 0
    exact map_zero _
  haveI : F.PreservesHomology := by
    apply Functor.preservesHomology_of_map_exact
    intro S hS
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
    exact IsLocalizedModule.map_exact q.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap q.asIdeal.primeCompl S.X₁)
      (LocalizedModule.mkLinearMap q.asIdeal.primeCompl S.X₂)
      (LocalizedModule.mkLinearMap q.asIdeal.primeCompl S.X₃) S.f.hom S.g.hom hS
  have hloc : ∀ i : ZMod 2, Limits.IsZero (F.obj (K.toCochainComplex.homology i)) := by
    intro i
    have hlen : IsFiniteLength R (K.toCochainComplex.homology i) := by
      fin_cases i
      · exact h₀
      · exact h₁
    change Limits.IsZero (ModuleCat.of (Localization.AtPrime q.asIdeal)
      (LocalizedModule.AtPrime q.asIdeal (K.toCochainComplex.homology i)))
    by_cases htriv : Subsingleton (K.toCochainComplex.homology i)
    · letI := htriv
      exact ModuleCat.isZero_of_subsingleton _
    · haveI : Nontrivial (K.toCochainComplex.homology i) :=
        not_subsingleton_iff_nontrivial.mp htriv
      haveI : IsNoetherian R (K.toCochainComplex.homology i) :=
        (isFiniteLength_iff_isNoetherian_isArtinian.mp hlen).1
      have hsupp := (Module.support_eq_singleton_closedPoint_iff_isFiniteLength
        (R := R) (M := K.toCochainComplex.homology i)).mpr hlen
      have hnot : q ∉ Module.support R (K.toCochainComplex.homology i) := by
        rw [hsupp]
        simpa only [Set.mem_singleton_iff] using hq_ne
      haveI : Subsingleton (LocalizedModule.AtPrime q.asIdeal (K.toCochainComplex.homology i)) :=
        Module.notMem_support_iff.mp hnot
      exact ModuleCat.isZero_of_subsingleton _
  intro i
  have hmap : ((K.toCochainComplex.sc i).map F).Exact := by
    apply (ShortComplex.exact_iff_isZero_homology _).mpr
    exact ((K.toCochainComplex.sc i).mapHomologyIso F).isZero_iff.mpr (hloc i)
  apply ShortComplex.exact_of_iso (S₁ := (K.toCochainComplex.sc i).map F) _ hmap
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  · simp [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
      HomologicalComplex.shortComplexFunctor', ShortComplex.map, F,
      toCochainComplex, CochainComplex.of.d, localizedAtPrime] <;> split_ifs <;> rfl
  · simp [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
      HomologicalComplex.shortComplexFunctor', ShortComplex.map, F,
      toCochainComplex, CochainComplex.of.d, localizedAtPrime] <;> split_ifs <;> rfl

end CategoryTheory.TwoPeriodicEndomorphism
