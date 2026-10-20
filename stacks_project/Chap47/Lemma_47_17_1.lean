module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.MinimalPrime

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsDualizingComplex

/- Lemma 47.17.1: for a dualizing complex over a Noetherian commutative ring, localization
at a minimal prime of its cohomology is nontrivial in exactly one integer degree. -/
@[stacks 0A7X] #check
  (CategoryTheory.DerivedCategory.IsDualizingComplex.existsUnique_localizedCohomology_nontrivial :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsDualizingComplex H)
    (p : PrimeSpectrum A) (hp : p.asIdeal ∈ minimalPrimes A),
    ∃! i : ℤ,
      Nontrivial
        (LocalizedModule.AtPrime p.asIdeal
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj ω)))

end CategoryTheory.DerivedCategory.IsDualizingComplex
