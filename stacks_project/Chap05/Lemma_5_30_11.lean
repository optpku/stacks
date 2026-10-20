module

public import Mathlib.Algebra.Category.ModuleCat.Topology.Basic
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

variable (R : Type u) [Ring R] [TopologicalSpace R] [IsTopologicalRing R]

/-
`TopModuleCat R` is the canonical owner used in Definition 5.30.10. Its limit and
forgetful-preservation instances exactly supply the three clauses here, so tagged proposition
checks avoid creating duplicate global instances. The installed owner is more general, but this
source-facing check block retains the source's `[IsTopologicalRing R]` setup.
-/

/- Lemma 5.30.11 (1): the category `TopModuleCat R` of topological `R`-modules has all small
limits. -/
@[stacks 0B26 "topological modules have all small limits"]
#check (inferInstance : HasLimits (TopModuleCat R))

/- Lemma 5.30.11 (2): the forgetful functor from `TopModuleCat R` to `TopCat` preserves all small
limits. -/
@[stacks 0B26 "limits commute with the forgetful functor to topological spaces"]
#check (inferInstance : PreservesLimits (forget₂ (TopModuleCat R) TopCat))

/- Lemma 5.30.11 (3): the forgetful functor from `TopModuleCat R` to `ModuleCat R` preserves all
small limits. -/
@[stacks 0B26 "limits commute with the forgetful functor to modules"]
#check (inferInstance : PreservesLimits (forget₂ (TopModuleCat R) (ModuleCat R)))
