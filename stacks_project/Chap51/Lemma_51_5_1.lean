/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Support
import StacksCheckRecall

universe u v w

/- Lemma 51.5.1 (1): for a Noetherian ring `A` and a specialization-stable
subset `T ⊆ PrimeSpectrum A`, `H⁰_T(M) = M` if and only if
`Module.support A M ⊆ T`. -/
@[stacks 0EEZ] #check
  (Module.sectionsWithSupport_eq_top_iff_support_subset :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
      (M : Type v) [AddCommGroup M] [Module A M],
      Module.sectionsWithSupport T M = ⊤ ↔ Module.support A M ⊆ T)

/- Lemma 51.5.1 (2): under the same source assumptions, the `A`-modules
supported on `T` form a Serre subcategory of `ModuleCat A`. -/
@[stacks 0EEZ] #check
  (CategoryTheory.ModuleCat.supportedOnIsSerreClass :
    ∀ {A : Type u} [CommRing A] (T : Set (PrimeSpectrum A)),
      CategoryTheory.ObjectProperty.IsSerreClass
        (CategoryTheory.ModuleCat.supportedOn T :
          CategoryTheory.ObjectProperty (ModuleCat.{v} A)))

/- Lemma 51.5.1 (3): under the same source assumptions, the `A`-modules
supported on `T` are closed under direct sums indexed by any type `I`. -/
@[stacks 0EEZ] #check
  (CategoryTheory.ModuleCat.supportedOnIsClosedUnderCoproducts :
    ∀ {A : Type u} [CommRing A] (T : Set (PrimeSpectrum A)) (I : Type w),
      CategoryTheory.ObjectProperty.IsClosedUnderColimitsOfShape
        (CategoryTheory.ModuleCat.supportedOn T :
          CategoryTheory.ObjectProperty (ModuleCat.{v} A))
        (CategoryTheory.Discrete I))
