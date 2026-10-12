/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.AlgebraizationSituation.LocalCompletion

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.DerivedCategory
open CategoryTheory.DerivedCategory.LocalCohomology
open CategoryTheory.DerivedCategory.LocalCohomology.Completion

universe u

/- Lemma 52.10.4 (1) -/
@[stacks 0EFR] #check (Ideal.LocalCohomology.AlgebraizationSituation.cohomologyToLimit_bijective :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (I : Ideal A) (M : ModuleCat.{u} A) [Module.Finite A M] (s d : ℤ)
      (h : Ideal.LocalCohomology.AlgebraizationSituation H I (M : Type u)
        ({IsLocalRing.closedPoint A} : Set (PrimeSpectrum A)) s d)
      (RΓm : DerivedCategory (ModuleCat.{u} A) ⥤
        IdealPowerTorsion (IsLocalRing.maximalIdeal A))
      (hRΓm : IdealPowerTorsion.inclusion (IsLocalRing.maximalIdeal A) ⊣ RΓm),
      ∀ i : ℤ, i ≤ s → Function.Bijective
        (cohomologyToLimit I (IsLocalRing.maximalIdeal A) RΓm M i))

/- Lemma 52.10.4 (2) -/
@[stacks 0EFR] #check (Ideal.LocalCohomology.AlgebraizationSituation.cohomology_annihilatedByPower :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (I : Ideal A) (M : ModuleCat.{u} A) [Module.Finite A M] (s d : ℤ)
      (h : Ideal.LocalCohomology.AlgebraizationSituation H I (M : Type u)
        ({IsLocalRing.closedPoint A} : Set (PrimeSpectrum A)) s d)
      (RΓm : DerivedCategory (ModuleCat.{u} A) ⥤
        IdealPowerTorsion (IsLocalRing.maximalIdeal A))
      (hRΓm : IdealPowerTorsion.inclusion (IsLocalRing.maximalIdeal A) ⊣ RΓm),
      ∀ i : ℤ, i ≤ s →
        Module.IsAnnihilatedByPower I
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
            (RΓm.obj (ModuleCat.single0 M)).obj) ∧
        Module.IsAnnihilatedByPower I
          ((limit (quotientSystem I (IsLocalRing.maximalIdeal A) RΓm M ⋙
            DerivedCategory.homologyFunctor (ModuleCat.{u} A) i)) : ModuleCat.{u} A))
