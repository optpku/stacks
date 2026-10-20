/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek.Normalized
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open ModuleCat
open UpperShriek

noncomputable section

universe u

/- Lemma 47.25.6 -/
@[stacks 0E9N] #check
  (CategoryTheory.ModuleCat.UpperShriek.Presentation.localizedObj_isNormalizedDualizingComplex :
    ∀ {R A : Type u} [CommRing R] [CommRing A]
    [IsNoetherianRing R] [IsNoetherianRing A] [IsLocalRing R]
    (φ : R →+* A) (hφ : φ.FiniteType) (p : Presentation φ)
    (m : MaximalSpectrum A)
    (hm : Ideal.comap φ m.asIdeal = IsLocalRing.maximalIdeal R)
    [MonoidalCategory (DerivedCategory (ModuleCat.{u, u} R))]
    [MonoidalCategory
      (DerivedCategory (ModuleCat.{u, u} (Localization.AtPrime m.asIdeal)))]
    (HR : MonoidalClosed (DerivedCategory (ModuleCat.{u, u} R)))
    (HAm : MonoidalClosed
      (DerivedCategory (ModuleCat.{u, u} (Localization.AtPrime m.asIdeal))))
    (ω : DerivedCategory (ModuleCat.{u, u} R))
    (hω : ω.IsNormalizedDualizingComplex HR),
    ((ModuleCat.derivedExtensionOfScalars
      (algebraMap A (Localization.AtPrime m.asIdeal))).obj
        (p.functor.obj ω)).IsNormalizedDualizingComplex HAm)
