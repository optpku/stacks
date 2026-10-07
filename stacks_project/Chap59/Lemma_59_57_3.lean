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
