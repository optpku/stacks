/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek.BaseChange.RelativeDualizing

@[expose] public section

open CategoryTheory
open ModuleCat
open UpperShriek
open Presentation

noncomputable section

universe u

/- Lemma 47.25.1 (1) -/
@[stacks 0BZV] #check
  (CategoryTheory.ModuleCat.UpperShriek.Presentation.relativeDualizingBaseChange_isIso_of_baseFlat :
    ∀ {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
      [Algebra R A] [Algebra R R'] [IsNoetherianRing R] [IsNoetherianRing R']
      [Algebra.FiniteType R A] [Module.Flat R R']
      (p : Presentation (algebraMap R A)),
      IsIso ((p.flatBaseChange R').app (ModuleCat.single0 (ModuleCat.of R R))))

/- Lemma 47.25.1 (2) -/
@[stacks 0BZV] #check
  (CategoryTheory.ModuleCat.UpperShriek.Presentation.relativeDualizingBaseChange_isIso_of_algebraFlat :
    ∀ {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
      [Algebra R A] [Algebra R R'] [IsNoetherianRing R] [IsNoetherianRing R']
      [Algebra.FiniteType R A] [Module.Flat R A]
      (p : Presentation (algebraMap R A)),
      IsIso ((p.baseChangeComparison R' (Tor.IsIndependent.of_flat_left R')).app
        (ModuleCat.single0 (ModuleCat.of R R))))

/- Lemma 47.25.1 (3) -/
@[stacks 0BZV] #check
  (CategoryTheory.ModuleCat.UpperShriek.Presentation.relativeDualizingBaseChange_isIso_of_isPerfect :
    ∀ {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
      [Algebra R A] [Algebra R R'] [IsNoetherianRing R] [IsNoetherianRing R']
      [Algebra.FiniteType R A] [(algebraMap R A).IsPerfectRingMap]
      (p : Presentation (algebraMap R A))
      (hTor : Tor.IsIndependent (ModuleCat.of R A) (ModuleCat.of R R')),
      IsIso ((p.baseChangeComparison R' hTor).app
        (ModuleCat.single0 (ModuleCat.of R R))))
