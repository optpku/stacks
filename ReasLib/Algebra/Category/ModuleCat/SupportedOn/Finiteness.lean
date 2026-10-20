/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.ClosedSupport
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleEmbedding
public import ReasLib.RingTheory.Flatness.LocallyFree

@[expose] public section

open CategoryTheory

universe u

namespace CategoryTheory.ModuleCat.SupportedOn

/-- Supported cohomology through degree `n` is finite exactly when a single ideal
whose zero locus lies in `T` annihilates every such degree. -/
theorem cohomology_finite_iff_exists_annihilator
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] (n : ℕ) :
    (∀ i : ℕ, i ≤ n →
      Module.Finite A (cohomology T (ModuleCat.single0 (ModuleCat.of A M)) (i : ℤ))) ↔
      ∃ J : Ideal A, PrimeSpectrum.zeroLocus (J : Set A) ⊆ T ∧
        ∀ i : ℕ, i ≤ n →
          J ≤ Module.annihilator A
            (cohomology T (ModuleCat.single0 (ModuleCat.of A M)) (i : ℤ)) := sorry

/-- For closed support `V(I)`, supported cohomology through degree `n` is finite
exactly when one power of `I` annihilates every such degree. -/
theorem cohomology_finite_iff_exists_power_annihilator
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] (n : ℕ) :
    (∀ i : ℕ, i ≤ n →
      Module.Finite A
        (cohomology (PrimeSpectrum.zeroLocus (I : Set A))
          (ModuleCat.single0 (ModuleCat.of A M)) (i : ℤ))) ↔
      ∃ e : ℕ, ∀ i : ℕ, i ≤ n →
        I ^ e ≤ Module.annihilator A
          (cohomology (PrimeSpectrum.zeroLocus (I : Set A))
            (ModuleCat.single0 (ModuleCat.of A M)) (i : ℤ)) := sorry

/-- Supported cohomology through degree `n` is finite exactly when all its
localizations at prime ideals are finite over the corresponding local rings. -/
theorem cohomology_finite_iff_localizedAtPrime_finite
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] (n : ℕ) :
    (∀ i : ℕ, i ≤ n →
      Module.Finite A
        (cohomology (PrimeSpectrum.zeroLocus (I : Set A))
          (ModuleCat.single0 (ModuleCat.of A M)) (i : ℤ))) ↔
      ∀ (p : PrimeSpectrum A) (i : ℕ), i ≤ n →
        Module.Finite (Localization.AtPrime p.asIdeal)
          (LocalizedModule.AtPrime p.asIdeal
            (cohomology (PrimeSpectrum.zeroLocus (I : Set A))
              (ModuleCat.single0 (ModuleCat.of A M)) (i : ℤ))) := sorry

/-- For a Noetherian ring and an ideal `I`, finiteness of supported cohomology
through degree `n` of the regular module on `V(I)` implies the same finiteness
for every finite module that is finite locally free after localization at each
element of `I`. -/
theorem cohomology_finite_of_finiteLocallyFreeAway
    {A M : Type u} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) (n : ℕ)
    (hA : ∀ i : ℕ, i ≤ n →
      Module.Finite A
        (cohomology (PrimeSpectrum.zeroLocus (I : Set A))
          (ModuleCat.single0 (ModuleCat.of A A)) (i : ℤ)))
    (hM : ∀ f ∈ I,
      Module.FiniteLocallyFree (Localization.Away f) (LocalizedModule.Away f M)) :
    ∀ i : ℕ, i ≤ n →
      Module.Finite A
        (cohomology (PrimeSpectrum.zeroLocus (I : Set A))
          (ModuleCat.single0 (ModuleCat.of A M)) (i : ℤ)) := sorry

end CategoryTheory.ModuleCat.SupportedOn
