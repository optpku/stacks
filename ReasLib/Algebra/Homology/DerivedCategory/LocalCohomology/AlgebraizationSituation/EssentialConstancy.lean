/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.AlgebraizationSituation
public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.AdicComparison
public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler
public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.Presentation
public import ReasLib.Algebra.Module.IdealPower.Predicate

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ModuleCat.SupportedOn Opposite

noncomputable section

universe u

namespace Ideal.LocalCohomology.AlgebraizationSituation

/-- The canonical adic quotient cohomology cone is essentially constant in every degree
at most the algebraization bound. -/
theorem adicCohomologyCone_isEssentiallyConstant
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (C : CategoryTheory.DerivedCategory.CanonicalClosedPresentation (A := A))
    (I : Ideal A) (M : Type u)
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (T : Set (PrimeSpectrum A)) (s d : ℤ)
    (h : AlgebraizationSituation C I M T s d) (i : ℤ) (hi : i ≤ s) :
    (CategoryTheory.ModuleCat.SupportedOn.adicComparisonCone T I
      (ModuleCat.of A M) i).IsEssentiallyConstant := sorry

/-- The canonical adic quotient cohomology inverse system satisfies the
Mittag-Leffler condition in every degree at most the algebraization bound. -/
theorem adicCohomologySystem_isMittagLeffler
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (C : CategoryTheory.DerivedCategory.CanonicalClosedPresentation (A := A))
    (I : Ideal A) (M : Type u)
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (T : Set (PrimeSpectrum A)) (s d : ℤ)
    (h : AlgebraizationSituation C I M T s d) (i : ℤ) (hi : i ≤ s) :
    CategoryTheory.SequentialInverseSystem.IsMittagLeffler
      (CategoryTheory.ModuleCat.SupportedOn.adicTower T I
        (ModuleCat.of A M) i) := sorry

/-- The supported cohomology of a finite module in an algebraization situation is
annihilated by one power of the defining ideal in every degree at most the bound. -/
theorem cohomology_isAnnihilatedByPower
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (C : CategoryTheory.DerivedCategory.CanonicalClosedPresentation (A := A))
    (I : Ideal A) (M : Type u)
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (T : Set (PrimeSpectrum A)) (s d : ℤ)
    (h : AlgebraizationSituation C I M T s d) (i : ℤ) (hi : i ≤ s) :
    Module.IsAnnihilatedByPower I
      (CategoryTheory.ModuleCat.SupportedOn.cohomology T
        (ModuleCat.single0Functor.obj (ModuleCat.of A M)) i) := sorry

/-- The canonical comparison from supported cohomology to the inverse limit of the
adic quotient tower is an isomorphism in every degree at most the bound. -/
theorem cohomologyLimitComparison_isIso
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (C : CategoryTheory.DerivedCategory.CanonicalClosedPresentation (A := A))
    (I : Ideal A) (M : Type u)
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (T : Set (PrimeSpectrum A)) (s d : ℤ)
    (h : AlgebraizationSituation C I M T s d) (i : ℤ) (hi : i ≤ s) :
    IsIso (CategoryTheory.ModuleCat.SupportedOn.adicLimitComparison T I
      (ModuleCat.of A M) i) := sorry

end Ideal.LocalCohomology.AlgebraizationSituation

end
