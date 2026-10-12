/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.AlgebraizationSituation.EssentialConstancy
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ModuleCat.SupportedOn Opposite

noncomputable section

universe u

namespace Ideal.LocalCohomology.AlgebraizationSituation

/- Theorem 52.10.8 (1) -/
@[stacks 0EIE] #check
  (Ideal.LocalCohomology.AlgebraizationSituation.adicCohomologyCone_isEssentiallyConstant :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (I : Ideal A) (M : Type u)
      [AddCommGroup M] [Module A M] [Module.Finite A M]
      (T : Set (PrimeSpectrum A)) (s d : ℤ)
      (h : AlgebraizationSituation H I M T s d) (i : ℤ) (hi : i ≤ s),
      (CategoryTheory.ModuleCat.SupportedOn.adicComparisonCone T I
        (ModuleCat.of A M) i).IsEssentiallyConstant)

/- Theorem 52.10.8 (2) -/
@[stacks 0EIE] #check
  (Ideal.LocalCohomology.AlgebraizationSituation.adicCohomologySystem_isMittagLeffler :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (I : Ideal A) (M : Type u)
      [AddCommGroup M] [Module A M] [Module.Finite A M]
      (T : Set (PrimeSpectrum A)) (s d : ℤ)
      (h : AlgebraizationSituation H I M T s d) (i : ℤ) (hi : i ≤ s),
      CategoryTheory.SequentialInverseSystem.IsMittagLeffler
        (CategoryTheory.ModuleCat.SupportedOn.adicTower T I
          (ModuleCat.of A M) i))

/- Theorem 52.10.8 (3) -/
@[stacks 0EIE] #check
  (Ideal.LocalCohomology.AlgebraizationSituation.cohomology_isAnnihilatedByPower :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (I : Ideal A) (M : Type u)
      [AddCommGroup M] [Module A M] [Module.Finite A M]
      (T : Set (PrimeSpectrum A)) (s d : ℤ)
      (h : AlgebraizationSituation H I M T s d) (i : ℤ) (hi : i ≤ s),
      Module.IsAnnihilatedByPower I
        (CategoryTheory.ModuleCat.SupportedOn.cohomology T
          (ModuleCat.single0Functor.obj (ModuleCat.of A M)) i))

/- Theorem 52.10.8 (4) -/
@[stacks 0EIE] #check
  (Ideal.LocalCohomology.AlgebraizationSituation.cohomologyLimitComparison_isIso :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (I : Ideal A) (M : Type u)
      [AddCommGroup M] [Module A M] [Module.Finite A M]
      (T : Set (PrimeSpectrum A)) (s d : ℤ)
      (h : AlgebraizationSituation H I M T s d) (i : ℤ) (hi : i ≤ s),
      IsIso (CategoryTheory.ModuleCat.SupportedOn.adicLimitComparison T I
        (ModuleCat.of A M) i))

end Ideal.LocalCohomology.AlgebraizationSituation

end
