module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension.FiniteCohomology
public import Mathlib.RingTheory.Finiteness.Basic

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsDualizingComplex

/-- Derived coextension along a finite homomorphism of Noetherian commutative rings
carries a dualizing complex over the source to a dualizing complex over the target. -/
theorem coextensionOfFinite
    {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} B))]
    (f : A →+* B) (hf : f.Finite)
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (HB : MonoidalClosed (DerivedCategory (ModuleCat.{u} B)))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsDualizingComplex HA) :
    ((CategoryTheory.ModuleCat.derivedCoextensionOfScalars f).obj ω).IsDualizingComplex HB := sorry

/-- Derived coextension along a surjective homomorphism of Noetherian commutative rings
carries a dualizing complex over the source to a dualizing complex over the target. -/
theorem coextensionOfSurjective
    {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} B))]
    (f : A →+* B) (hf : Function.Surjective f)
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (HB : MonoidalClosed (DerivedCategory (ModuleCat.{u} B)))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsDualizingComplex HA) :
    ((CategoryTheory.ModuleCat.derivedCoextensionOfScalars f).obj ω).IsDualizingComplex HB := sorry

end CategoryTheory.DerivedCategory.IsDualizingComplex
