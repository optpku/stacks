module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Localization
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Uniqueness
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Invertible
public import ReasLib.RingTheory.Gorenstein.Ring
public import Mathlib.Topology.Basic

@[expose] public section

open CategoryTheory
open DerivedCategory.DerivedTensor.Right.Monoidal

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsDualizingComplex

/-- The Gorenstein property of a Noetherian ring is characterized by
tensor-invertibility of any chosen dualizing complex. -/
theorem gorenstein_iff_isInvertibleObject
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [BraidedCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : @Model (ModuleCat.{u} A) _ _ _ _ _ _ _)
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsDualizingComplex H) :
    IsGorensteinRing A ↔ MonoidalCategory.isInvertibleObject ω := sorry

/-- At a prime, the localized ring is Gorenstein exactly when the localized
dualizing complex is tensor-invertible. -/
theorem localization_gorenstein_iff_isInvertibleObject
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [BraidedCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : @Model (ModuleCat.{u} A) _ _ _ _ _ _ _)
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsDualizingComplex H)
    (p : PrimeSpectrum A)
    [MonoidalCategory
      (DerivedCategory (ModuleCat.{u} (Localization.AtPrime p.asIdeal)))]
    (Tp : @Model (ModuleCat.{u} (Localization.AtPrime p.asIdeal)) _ _ _ _ _ _ _) :
    IsGorensteinLocalRing (Localization.AtPrime p.asIdeal) ↔
      MonoidalCategory.isInvertibleObject
        ((ModuleCat.derivedExtensionOfScalars
          (algebraMap A (Localization.AtPrime p.asIdeal))).obj ω) := sorry

/-- The subset of the prime spectrum where the localization is Gorenstein is
open. -/
theorem isOpen_gorensteinLocus
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [BraidedCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : @Model (ModuleCat.{u} A) _ _ _ _ _ _ _)
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsDualizingComplex H) :
    IsOpen { p : PrimeSpectrum A |
      IsGorensteinLocalRing (Localization.AtPrime p.asIdeal) } := sorry

/-- For a Gorenstein ring, a dualizing complex exists exactly when the regular
module concentrated in degree zero is dualizing. -/
theorem exists_iff_ringSingle
    (A : Type u) [CommRing A] [IsGorensteinRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [BraidedCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : @Model (ModuleCat.{u} A) _ _ _ _ _ _ _) :
    (∃ ω : DerivedCategory (ModuleCat.{u} A), ω.IsDualizingComplex H) ↔
      (ModuleCat.single0 (ModuleCat.of A A)).IsDualizingComplex H := sorry

end CategoryTheory.DerivedCategory.IsDualizingComplex
