module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek.BaseChange.Perfect

@[expose] public section

open CategoryTheory
open ModuleCat
open UpperShriek
open Presentation
open scoped TensorProduct

noncomputable section

universe u

/-- A flat algebra in the left tensor factor is Tor independent from every other algebra over
its base ring. -/
theorem torIndependentOfFlatLeft
    {R A : Type u} (R' : Type u) [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R'] [Module.Flat R A] :
    Tor.IsIndependent (ModuleCat.of R A) (ModuleCat.of R R') :=
  CategoryTheory.ModuleCat.Tor.IsIndependent.of_flat_left R'

/- Lemma 47.24.6: if `R` and `R'` are Noetherian and `R → A` is flat and of finite type,
the upper-shriek base-change comparison is invertible as a natural transformation. -/
@[stacks 0BZS] #check
  (CategoryTheory.ModuleCat.UpperShriek.baseChangeComparison_isIso_of_flat_finiteType :
    ∀ {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
      [Algebra R A] [Algebra R R'] [IsNoetherianRing R] [IsNoetherianRing R']
      [Module.Flat R A] [Algebra.FiniteType R A]
      (p : Presentation (algebraMap R A)),
      IsIso (p.baseChangeComparison R'
        (CategoryTheory.ModuleCat.Tor.IsIndependent.of_flat_left R')))
