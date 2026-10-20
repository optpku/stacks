/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.AlgebraizationSituation.AdicCohomology
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ModuleCat.SupportedOn
open scoped ZeroObject

noncomputable section

universe u

/- Lemma 52.10.6 (1): in Situation 52.10.1, the inverse systems of supported local
cohomology modules of the adic stages are pro-zero in every degree `i ≤ s`. -/
@[stacks 0EFX] #check (Ideal.LocalCohomology.AlgebraizationSituation.proZero_adicCohomology :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (I : Ideal A) (M : Type u)
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (T : Set (PrimeSpectrum A)) (s d : ℤ)
    (h : Ideal.LocalCohomology.AlgebraizationSituation H I M T s d),
    ∀ i : ℤ, i ≤ s →
      CategoryTheory.Pro.HasValue
        (supportedCohomologyTower T
          (Ideal.PowerSubmodule.system I (ModuleCat.of A M)) i)
        (0 : ModuleCat.{u} A))

/- Lemma 52.10.6 (2): in Situation 52.10.1, the images in degree `s + 1` eventually
map injectively into one fixed stage of the supported local-cohomology tower. -/
@[stacks 0EFX] #check (Ideal.LocalCohomology.AlgebraizationSituation.exists_eventually_mono_adicCohomology :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (I : Ideal A) (M : Type u)
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (T : Set (PrimeSpectrum A)) (s d : ℤ)
    (h : Ideal.LocalCohomology.AlgebraizationSituation H I M T s d),
    ∃ (m₀ : ℕ), ∀ (m : ℕ) (h_m₀m : m₀ ≤ m),
      ∃ (m' : ℕ) (h_mm' : m ≤ m'), ∀ (k : ℕ) (h_m'k : m' ≤ k),
        Mono
          ((imageSubobject
              ((supportedCohomologyTower T
                (Ideal.PowerSubmodule.system I (ModuleCat.of A M)) (s + 1)).transitionMap
                (Nat.le_trans h_mm' h_m'k))).arrow ≫
            (supportedCohomologyTower T
              (Ideal.PowerSubmodule.system I (ModuleCat.of A M)) (s + 1)).transitionMap
              h_m₀m))
