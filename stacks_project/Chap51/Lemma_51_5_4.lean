/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.BoundedComparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 51.5.4: for a specialization-stable subset `T ⊆ PrimeSpectrum A`, the
canonical functor from `D⁺(Mod_{A,T})` to the bounded-below derived objects of
`A`-modules whose cohomology is supported on `T` is an equivalence. -/
@[stacks 0EF2] #check
  (CategoryTheory.ModuleCat.SupportedOn.boundedBelowComparisonIsEquivalence :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      (T : Set (PrimeSpectrum A)) [Fact (StableUnderSpecialization T)],
      Functor.IsEquivalence
        (DerivedCategory.Plus.CohomologyIn.Comparison.functor
          (ModuleCat.supportedOn T : ObjectProperty (ModuleCat.{u} A))))
