module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek.BaseChange.Perfect

@[expose] public section

open CategoryTheory
open ModuleCat
open UpperShriek

noncomputable section

universe u

/- Lemma 47.24.5 -/
@[stacks 0BZR] #check
  (CategoryTheory.ModuleCat.UpperShriek.baseChangeComparison_isIso_of_isPerfect :
    ∀ {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
      [Algebra R A] [Algebra R R'] [IsNoetherianRing R] [IsNoetherianRing R']
      [(algebraMap R A).IsPerfectRingMap]
      (p : CategoryTheory.ModuleCat.UpperShriek.Presentation (algebraMap R A))
      (hTor : CategoryTheory.ModuleCat.Tor.IsIndependent
        (ModuleCat.of R A) (ModuleCat.of R R')),
      IsIso (p.baseChangeComparison R' hTor))
