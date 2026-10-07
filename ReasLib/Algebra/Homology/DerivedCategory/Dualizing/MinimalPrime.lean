module

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Localization
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized.ZeroDimensional
public import ReasLib.RingTheory.KrullDimension.Prime

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsDualizingComplex

/-- For a dualizing complex over a Noetherian commutative ring, localization of its
cohomology at a minimal prime is nontrivial in exactly one integer degree. -/
theorem existsUnique_localizedCohomology_nontrivial
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsDualizingComplex H)
    (p : PrimeSpectrum A) (hp : p.asIdeal ∈ minimalPrimes A) :
    ∃! i : ℤ,
      Nontrivial
        (LocalizedModule.AtPrime p.asIdeal
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj ω)) := sorry

end CategoryTheory.DerivedCategory.IsDualizingComplex
