/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek.FiberDimension
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open ModuleCat.UpperShriek

noncomputable section

universe u

/- Lemma 47.25.7: for a finite-type map of Noetherian rings, nonvanishing at `q` of
degree-`i` cohomology of the relative dualizing complex associated to a polynomial
presentation forces `-(d : ℤ) ≤ i`, where `d` is the dimension of the fibre over `p` at
`q`. -/
@[stacks 0E9P] #check
  (CategoryTheory.ModuleCat.UpperShriek.Presentation.neg_fiberDimension_le_of_localizedCohomology_nontrivial :
    ∀ {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
      [IsNoetherianRing R] [IsNoetherianRing A]
      (hf : (algebraMap R A).FiniteType)
      (presentation : Presentation (algebraMap R A))
      (p : PrimeSpectrum R) (q : PrimeSpectrum A)
      (hq : PrimeSpectrum.comap (algebraMap R A) q = p)
      (d : ℕ)
      (hd : topologicalKrullDimAt (fiberPrimeAt R A q) = (d : WithBot ℕ∞))
      (i : ℤ)
      (hi : Nontrivial
        (LocalizedModule.AtPrime q.asIdeal
          ((DerivedCategory.homologyFunctor (ModuleCat.{u, u} A) i).obj
            (presentation.functor.obj (ModuleCat.single0 (ModuleCat.of R R)))))),
      -(d : ℤ) ≤ i)
