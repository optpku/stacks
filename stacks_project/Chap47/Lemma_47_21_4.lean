module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Gorenstein
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open DerivedCategory.DerivedTensor.Right.Monoidal

noncomputable section

universe u

/- Lemma 47.21.4 (1): A Noetherian commutative ring with a dualizing complex is
Gorenstein if and only if that complex is tensor-invertible in its derived category. -/
@[stacks 0DW9] #check
  (CategoryTheory.DerivedCategory.IsDualizingComplex.gorenstein_iff_isInvertibleObject :
    ∀ (A : Type u) [CommRing A] [IsNoetherianRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      [BraidedCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (T : @Model (ModuleCat.{u} A) _ _ _ _ _ _ _)
      (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsDualizingComplex H),
      IsGorensteinRing A ↔ MonoidalCategory.isInvertibleObject ω)

/- Lemma 47.21.4 (2): At every prime of a Noetherian commutative ring carrying a
dualizing complex, the local ring is Gorenstein if and only if the localized complex is
tensor-invertible. -/
@[stacks 0DW9] #check
  (CategoryTheory.DerivedCategory.IsDualizingComplex.localization_gorenstein_iff_isInvertibleObject :
    ∀ (A : Type u) [CommRing A] [IsNoetherianRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      [BraidedCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (T : @Model (ModuleCat.{u} A) _ _ _ _ _ _ _)
      (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsDualizingComplex H)
      (p : PrimeSpectrum A)
      [MonoidalCategory
        (DerivedCategory (ModuleCat.{u} (Localization.AtPrime p.asIdeal)))]
      (Tp : @Model (ModuleCat.{u} (Localization.AtPrime p.asIdeal)) _ _ _ _ _ _ _),
      IsGorensteinLocalRing (Localization.AtPrime p.asIdeal) ↔
        MonoidalCategory.isInvertibleObject
          ((ModuleCat.derivedExtensionOfScalars
            (algebraMap A (Localization.AtPrime p.asIdeal))).obj ω))

/- Lemma 47.21.4 (3): The locus where the prime localization of a Noetherian
commutative ring with a dualizing complex is Gorenstein is open. -/
@[stacks 0DW9] #check
  (CategoryTheory.DerivedCategory.IsDualizingComplex.isOpen_gorensteinLocus :
    ∀ (A : Type u) [CommRing A] [IsNoetherianRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      [BraidedCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (T : @Model (ModuleCat.{u} A) _ _ _ _ _ _ _)
      (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsDualizingComplex H),
      IsOpen { p : PrimeSpectrum A |
        IsGorensteinLocalRing (Localization.AtPrime p.asIdeal) })

/- Lemma 47.21.4 (4): For a Gorenstein ring, existence of a dualizing complex is
equivalent to the regular module in degree zero being dualizing. -/
@[stacks 0DW9] #check
  (CategoryTheory.DerivedCategory.IsDualizingComplex.exists_iff_ringSingle :
    ∀ (A : Type u) [CommRing A] [IsGorensteinRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      [BraidedCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (T : @Model (ModuleCat.{u} A) _ _ _ _ _ _ _),
      (∃ ω : DerivedCategory (ModuleCat.{u} A), ω.IsDualizingComplex H) ↔
        (ModuleCat.single0 (ModuleCat.of A A)).IsDualizingComplex H)
