/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 51.5.5: for a specialization-stable subset `T ⊆ PrimeSpectrum A` and a
Noetherian ring of finite Krull dimension, the canonical functor from the derived category
of modules supported on `T` to derived objects whose cohomology is supported on `T` is an
equivalence. -/
@[stacks 0EF3] #check
  (CategoryTheory.ModuleCat.SupportedOn.comparisonIsEquivalence :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      (T : Set (PrimeSpectrum A)) [Fact (StableUnderSpecialization T)]
      [Fact (∃ d : ℕ, Ring.KrullDimLE d A)],
      Functor.IsEquivalence
        (DerivedCategory.CohomologyIn.Comparison.functor
          (ModuleCat.supportedOn T : ObjectProperty (ModuleCat.{u} A))))
