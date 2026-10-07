module

import StacksCheckRecall
import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek.Dualizing

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.UpperShriek

variable {R A : Type u} [CommRing R] [CommRing A]

/- Lemma 47.24.3 -/
@[stacks 0BZL] #check (CategoryTheory.ModuleCat.UpperShriek.Presentation.mapsDualizingComplex :
  ∀ {R A : Type u} [CommRing R] [CommRing A]
    [IsNoetherianRing R] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u, u} R))]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u, u} A))]
    (f : R →+* A) (hf : f.FiniteType) (p : CategoryTheory.ModuleCat.UpperShriek.Presentation f)
    (HR : MonoidalClosed (DerivedCategory (ModuleCat.{u, u} R)))
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u, u} A)))
    (ω : DerivedCategory (ModuleCat.{u, u} R)) (hω : ω.IsDualizingComplex HR),
    (p.functor.obj ω).IsDualizingComplex HA)

end CategoryTheory.ModuleCat.UpperShriek
