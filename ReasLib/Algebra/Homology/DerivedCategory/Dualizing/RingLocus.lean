module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.ModuleLocus
public import ReasLib.RingTheory.CohenMacaulay.Locus

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsDualizingComplex

/-- For a Noetherian commutative ring with a dualizing complex, the Cohen–Macaulay
locus of its prime spectrum is open. -/
theorem isOpen_cohenMacaulayRingLocus
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsDualizingComplex H) :
    IsOpen (PrimeSpectrum.cohenMacaulayLocus A) := sorry

/-- For a Noetherian commutative ring with a dualizing complex, the Cohen–Macaulay
locus of its prime spectrum is dense. -/
theorem dense_cohenMacaulayRingLocus
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsDualizingComplex H) :
    Dense (PrimeSpectrum.cohenMacaulayLocus A) := sorry

end CategoryTheory.DerivedCategory.IsDualizingComplex
