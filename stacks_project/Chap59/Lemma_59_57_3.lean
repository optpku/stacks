/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Cohomology

@[expose] public section

open CategoryTheory

/- Lemma 59.57.3 -/
@[stacks 0DVD] #check
  (CategoryTheory.Action.ModuleCat.DiscreteModuleCat.instIsIsoForgetComparison :
    ∀ (R G : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      (i : ℕ),
      IsIso (CategoryTheory.Action.ModuleCat.DiscreteModuleCat.forgetComparison R G i))
