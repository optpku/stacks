/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.Localization
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 51.4.6: the cohomological dimension of a finitely generated ideal is the maximum
of the cohomological dimensions of its extensions to all prime localizations. -/
@[stacks 0DXB] #check (Ideal.LocalCohomology.dimension_isGreatest_atPrime :
  ∀ {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG),
    IsGreatest
      (insert (-1) (Set.range (fun p : PrimeSpectrum A ↦
        Ideal.LocalCohomology.dimension
          (I.map (algebraMap A (Localization.AtPrime p.asIdeal)))
          (hI.map (algebraMap A (Localization.AtPrime p.asIdeal))))))
      (Ideal.LocalCohomology.dimension I hI))
