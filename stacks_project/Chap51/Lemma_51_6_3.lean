/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.Algebra.Category.ModuleCat.SupportedOn.Sequential

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Set TopologicalSpace

universe u

namespace CategoryTheory.ModuleCat.SupportedOn

/- Lemma 51.6.3: under the pointwise eventual vanishing, image stabilization,
and injectivity hypotheses for a specialization-stable subset of the spectrum,
the supported local-cohomology images are eventually injective into one fixed
stage. -/
@[stacks 0EFA] #check (CategoryTheory.ModuleCat.SupportedOn.exists_eventually_mono_supportedCohomology :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [FiniteRingKrullDim A]
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
            localCohomologyTransitionMap F i (Nat.zero_le m) p)),
    ∃ (m₀ : ℕ), ∀ (m : ℕ) (h_m₀m : m₀ ≤ m),
      ∃ (m'' : ℕ) (h_mm'' : m ≤ m''), ∀ (k : ℕ) (h_m''k : m'' ≤ k),
      Mono
        ((imageSubobject
            ((supportedCohomologyTower T F i).transitionMap
              (Nat.le_trans h_mm'' h_m''k))).arrow ≫
          (supportedCohomologyTower T F i).transitionMap h_m₀m))

end CategoryTheory.ModuleCat.SupportedOn
