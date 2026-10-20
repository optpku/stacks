/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.Derived
public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.NonminimalPrimeSequence
public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.PointTerms
public import ReasLib.RingTheory.KrullDimension.Finite
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Topology.KrullDimension

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Set TopologicalSpace

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.SupportedOn

variable {A : Type u} [CommRing A]

/-- The sequential inverse system of `i`th local cohomology modules supported on `T`,
obtained by applying the degree-zero embedding, derived supported sections,
the ambient inclusion, and degree-`i` homology to a module tower. -/
noncomputable abbrev supportedCohomologyTower
    (T : Set (PrimeSpectrum A)) (F : SequentialInverseSystem (ModuleCat.{u} A)) (i : ℤ) :
    SequentialInverseSystem (ModuleCat.{u} A) :=
  F ⋙ ModuleCat.single0Functor ⋙ derivedSections T ⋙ derivedInclusion T ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{u} A) i

/-- The localized module map induced by a transition map of an inverse system. -/
noncomputable def localizedModuleTransitionMap
    (F : SequentialInverseSystem (ModuleCat.{u} A)) {m k : ℕ} (hmk : m ≤ k)
    (p : PrimeSpectrum A) :
    ModuleCat.of (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal (F.obj (op k))) ⟶
      ModuleCat.of (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal (F.obj (op m))) :=
  ModuleCat.ofHom
    (LocalizedModule.map p.asIdeal.primeCompl (F.transitionMap hmk).hom)

/-- The local-cohomology map at `p` induced by a transition in the module tower. -/
noncomputable def localCohomologyTransitionMap
    (F : SequentialInverseSystem (ModuleCat.{u} A)) (i : ℤ) {m k : ℕ} (hmk : m ≤ k)
    (p : PrimeSpectrum A) :
    cohomology (PrimeSpectrum.zeroLocus (extendedPrime p))
        (ModuleCat.single0Functor.obj
          (ModuleCat.of (Localization.AtPrime p.asIdeal)
            (LocalizedModule.AtPrime p.asIdeal (F.obj (op k))))) i ⟶
      cohomology (PrimeSpectrum.zeroLocus (extendedPrime p))
        (ModuleCat.single0Functor.obj
          (ModuleCat.of (Localization.AtPrime p.asIdeal)
            (LocalizedModule.AtPrime p.asIdeal (F.obj (op m))))) i :=
  cohomologyMap (PrimeSpectrum.zeroLocus (extendedPrime p))
    (ModuleCat.single0Functor.map (localizedModuleTransitionMap F hmk p)) i

/-- Over a finite-dimensional Noetherian ring, uniform eventual vanishing of the
localized point-term transitions implies vanishing of supported local-cohomology
transitions after `2 ^ ((topologicalKrullDim T).unbotD 0).toNat` iterations of the
stabilization function. For nonempty `T` the exponent is its finite Krull dimension;
for empty `T` it is normalized to zero, and supported local cohomology vanishes. -/
theorem eventuallyZeroSupportedCohomology
    [IsNoetherianRing A] [FiniteRingKrullDim A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (F : SequentialInverseSystem (ModuleCat.{u} A)) (i : ℤ) (hi : 0 ≤ i)
    (m' : ℕ → ℕ) (hm'_ge : ∀ m, m ≤ m' m)
    (h_local : ∀ (m k : ℕ) (h_m'k : m' m ≤ k),
      ∀ (p : PrimeSpectrum A) (hp : p ∈ T),
        localCohomologyTransitionMap F i (Nat.le_trans (hm'_ge m) h_m'k) p = 0) :
    ∀ (m k : ℕ) (hmk : m ≤ k),
        (m'^[2 ^ ((topologicalKrullDim T).unbotD 0).toNat]) m ≤ k →
        (supportedCohomologyTower T F i).transitionMap hmk = 0 := sorry

/-- Over a finite-dimensional Noetherian ring, pointwise eventual vanishing of
the degree-`i - 1` localized transitions, stabilization of degree-`i` images,
and injectivity of those stabilized images into stage zero imply eventual
injectivity of supported degree-`i` images into one fixed stage. -/
theorem exists_eventually_mono_supportedCohomology
    [IsNoetherianRing A] [FiniteRingKrullDim A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (F : SequentialInverseSystem (ModuleCat.{u} A)) (i : ℤ) (hi : 0 ≤ i)
    (h_local : ∀ m : ℕ, ∃ (m' : ℕ) (h_m'ge : m ≤ m'),
      ∀ (p : PrimeSpectrum A), p ∈ T →
        (∀ (k : ℕ) (h_m'k : m' ≤ k),
          localCohomologyTransitionMap F (i - 1)
            (Nat.le_trans h_m'ge h_m'k) p = 0) ∧
        (∀ (k : ℕ) (h_m'k : m' ≤ k),
          imageSubobject
              (localCohomologyTransitionMap F i
                (Nat.le_trans h_m'ge h_m'k) p) =
            imageSubobject
              (localCohomologyTransitionMap F i h_m'ge p)) ∧
        Mono
          ((imageSubobject
              (localCohomologyTransitionMap F i h_m'ge p)).arrow ≫
            localCohomologyTransitionMap F i (Nat.zero_le m) p)) :
    ∃ (m₀ : ℕ), ∀ (m : ℕ) (h_m₀m : m₀ ≤ m),
      ∃ (m'' : ℕ) (h_mm'' : m ≤ m''), ∀ (k : ℕ) (h_m''k : m'' ≤ k),
      Mono
        ((imageSubobject
            ((supportedCohomologyTower T F i).transitionMap
              (Nat.le_trans h_mm'' h_m''k))).arrow ≫
          (supportedCohomologyTower T F i).transitionMap h_m₀m) := sorry

end CategoryTheory.ModuleCat.SupportedOn
