module

public import Mathlib.RingTheory.Localization.Submodule
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsDualizingComplex

/-- Derived scalar extension to a localization sends a dualizing complex over a Noetherian
commutative ring to a dualizing complex over the localized ring. -/
theorem localization
    {A : Type u} [CommRing A] [IsNoetherianRing A] (S : Submonoid A)
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} (Localization S)))]
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (HB : MonoidalClosed (DerivedCategory (ModuleCat.{u} (Localization S))))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsDualizingComplex HA) :
    ((ModuleCat.derivedExtensionOfScalars
      (algebraMap A (Localization S))).obj ω).IsDualizingComplex HB := sorry

end CategoryTheory.DerivedCategory.IsDualizingComplex
