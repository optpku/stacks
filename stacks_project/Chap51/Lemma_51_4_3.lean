/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension

/- Lemma 51.4.3 -/
@[stacks 0DX9] #check (Ideal.LocalCohomology.dimension_le_generatorCount :
  ∀ {A : Type _} [CommRing A] (I : Ideal A) (hI : I.FG)
    (G : I.FiniteGeneratingFamily), Ideal.LocalCohomology.dimension I hI ≤ (G.count : ℤ))

#check (Ideal.LocalCohomology.dimension_le_of_zeroLocus_eq :
  ∀ {A : Type _} [CommRing A] (I : Ideal A) (hI : I.FG) {r : ℕ} (f : Fin r → A),
    PrimeSpectrum.zeroLocus (Ideal.span (Set.range f) : Set A) =
        PrimeSpectrum.zeroLocus (I : Set A) →
      Ideal.LocalCohomology.dimension I hI ≤ (r : ℤ))

#check (Ideal.LocalCohomology.dimension_le_of_complement_hasCard :
  ∀ {A : Type _} [CommRing A] (I : Ideal A) (hI : I.FG) {c : ℕ},
    AlgebraicGeometry.Scheme.AffineOpenCover.HasCard
        (AlgebraicGeometry.Scheme.Modules.idealComplementOpens I).toScheme c →
      Ideal.LocalCohomology.dimension I hI ≤ (c : ℤ))
