/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek.RelativeDualizing.Bounds

@[expose] public section

open CategoryTheory
open CategoryTheory.ModuleCat.UpperShriek

noncomputable section

universe u

/- Lemma 47.25.9 (1) -/
@[stacks 0E9R] #check (CategoryTheory.ModuleCat.UpperShriek.Presentation.localizedCohomology_lowerBound :
    ∀ {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
      [IsNoetherianRing R] [IsNoetherianRing A]
      (hf : (algebraMap R A).FiniteType) (presentation : Presentation (algebraMap R A))
      (p : PrimeSpectrum R)
      (hp : Module.CohenMacaulay (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal))
      (r : ℕ)
      (htrdeg : ∀ q : minimalPrimes A,
        Ideal.ResidueField.trdeg (q.1.under R) q.1 ≤ (r : Cardinal))
      (i : ℤ)
      (hi : Nontrivial
        (LocalizedModule (Algebra.algebraMapSubmonoid A p.asIdeal.primeCompl)
          ((DerivedCategory.homologyFunctor (ModuleCat.{u, u} A) i).obj
            (presentation.functor.obj (ModuleCat.single0 (ModuleCat.of R R)))))) ,
      -(r : ℤ) ≤ i)

/- Lemma 47.25.9 (2) -/
@[stacks 0E9R] #check (CategoryTheory.ModuleCat.UpperShriek.Presentation.localizedCohomology_serreConditionSTwo :
    ∀ {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
      [IsNoetherianRing R] [IsNoetherianRing A]
      (hf : (algebraMap R A).FiniteType) (presentation : Presentation (algebraMap R A))
      (p : PrimeSpectrum R)
      (hp : Module.CohenMacaulay (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal))
      (r : ℕ)
      (htrdeg : ∀ q : minimalPrimes A,
        Ideal.ResidueField.trdeg (q.1.under R) q.1 ≤ (r : Cardinal)),
      Module.SerreConditionS
        (Localization (Algebra.algebraMapSubmonoid A p.asIdeal.primeCompl))
        (LocalizedModule (Algebra.algebraMapSubmonoid A p.asIdeal.primeCompl)
          ((DerivedCategory.homologyFunctor (ModuleCat.{u, u} A) (-(r : ℤ))).obj
            (presentation.functor.obj (ModuleCat.single0 (ModuleCat.of R R))))) 2)
