/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension.TopDimension
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.DerivedCategory
open CategoryTheory.DerivedCategory.LocalCohomology

universe u

namespace Ideal.LocalCohomology

/- Lemma 51.16.2: if a finite module supported on every top-dimensional irreducible
component has vanishing degree-`d` local cohomology, then the local-cohomological
dimension of `I` is strictly less than `d`. -/
@[stacks 0EB2] #check
  (Ideal.LocalCohomology.dimension_lt_of_topCohomology_isZero :
    ∀ {A M : Type u} [CommRing A] [IsNoetherianRing A] [AddCommGroup M]
      [Module A M] [Module.Finite A M]
      (I : Ideal A) (d : ℕ) (hdim : ringKrullDim A = d)
      (RΓ : DerivedCategory (ModuleCat A) ⥤ DerivedCategory.IdealPowerTorsion I)
      (hRΓ : DerivedCategory.IdealPowerTorsion.inclusion I ⊣ RΓ)
      (h_support : ∀ p ∈ minimalPrimes.topDim A,
        PrimeSpectrum.zeroLocus p ⊆ Module.support A M)
      (h_vanish : IsZero (supportedCohomology I RΓ (ModuleCat.of A M) (d : ℤ)))
      , dimension I I.fg_of_isNoetherianRing < (d : ℤ))

end Ideal.LocalCohomology
