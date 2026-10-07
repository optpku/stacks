module

public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.Derived
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Comparison.Plus

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.SupportedOn

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- For a Noetherian ring and specialization-stable support, the bounded-below
comparison from supported modules to complexes with supported cohomology is an equivalence. -/
noncomputable instance boundedBelowComparisonIsEquivalence
    (T : Set (PrimeSpectrum A)) [hT : Fact (StableUnderSpecialization T)] :
    Functor.IsEquivalence
      (DerivedCategory.Plus.CohomologyIn.Comparison.functor
        (ModuleCat.supportedOn T : ObjectProperty (ModuleCat.{u} A))) := sorry

end CategoryTheory.ModuleCat.SupportedOn
