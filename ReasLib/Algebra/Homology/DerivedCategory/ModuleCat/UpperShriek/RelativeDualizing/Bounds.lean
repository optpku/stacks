module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek.FiberDimension
public import ReasLib.RingTheory.CohenMacaulay.Module
public import ReasLib.RingTheory.CohenMacaulay.SerreCondition
public import ReasLib.RingTheory.Ideal.MinimalPrime.Localization
public import ReasLib.RingTheory.LocalRing.ResidueField.Transcendence

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.UpperShriek.Presentation

/-- For a finite-type map of Noetherian rings with Cohen–Macaulay localization at
`p` and bounded minimal-prime residue-field transcendence degree, nonzero
localized relative-dualizing cohomology occurs only in degrees at least `-r`. -/
theorem localizedCohomology_lowerBound
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
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
          (presentation.functor.obj (ModuleCat.single0 (ModuleCat.of R R)))))) :
    -(r : ℤ) ≤ i := sorry

/-- Under the same finite-type, Cohen–Macaulay, and transcendence-degree
hypotheses, the degree `-r` localized relative-dualizing cohomology module
satisfies Serre's condition `(S₂)`. -/
theorem localizedCohomology_serreConditionSTwo
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsNoetherianRing A]
    (hf : (algebraMap R A).FiniteType) (presentation : Presentation (algebraMap R A))
    (p : PrimeSpectrum R)
    (hp : Module.CohenMacaulay (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal))
    (r : ℕ)
    (htrdeg : ∀ q : minimalPrimes A,
      Ideal.ResidueField.trdeg (q.1.under R) q.1 ≤ (r : Cardinal)) :
    Module.SerreConditionS
      (Localization (Algebra.algebraMapSubmonoid A p.asIdeal.primeCompl))
      (LocalizedModule (Algebra.algebraMapSubmonoid A p.asIdeal.primeCompl)
        ((DerivedCategory.homologyFunctor (ModuleCat.{u, u} A) (-(r : ℤ))).obj
          (presentation.functor.obj (ModuleCat.single0 (ModuleCat.of R R))))) 2 := sorry

end CategoryTheory.ModuleCat.UpperShriek.Presentation
