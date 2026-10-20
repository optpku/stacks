module

public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.FlatExtension
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized
public import ReasLib.RingTheory.RingHom.Local.MaximalIdeal

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex

/-- Flat extension along a local homomorphism preserving the maximal ideal carries a normalized
dualizing complex to a normalized dualizing complex. -/
theorem baseChange_of_flat_of_mapsMaximalIdeal
    {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} B))]
    (f : A →+* B) [IsLocalHom f] (hflat : f.Flat) (hmax : f.MapsMaximalIdeal)
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (HB : MonoidalClosed (DerivedCategory (ModuleCat.{u} B)))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsNormalizedDualizingComplex HA) :
    ((ModuleCat.derivedExtensionOfScalars f).obj ω).IsNormalizedDualizingComplex HB := sorry

end CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex
