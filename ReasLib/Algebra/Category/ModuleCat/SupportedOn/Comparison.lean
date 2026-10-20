module

public import Mathlib.RingTheory.KrullDimension.Basic
public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.BoundedComparison

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.SupportedOn

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- For a Noetherian ring of finite Krull dimension and specialization-stable support,
the unbounded derived comparison from supported modules is an equivalence. -/
noncomputable instance comparisonIsEquivalence
    (T : Set (PrimeSpectrum A)) [hT : Fact (StableUnderSpecialization T)]
    [hfinite : Fact (∃ d : ℕ, Ring.KrullDimLE d A)] :
    Functor.IsEquivalence
      (DerivedCategory.CohomologyIn.Comparison.functor
        (ModuleCat.supportedOn T : ObjectProperty (ModuleCat.{u} A))) := sorry

end CategoryTheory.ModuleCat.SupportedOn
