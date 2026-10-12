/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Topology.Basic
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

universe u

variable (R : Type u) [Ring R] [TopologicalSpace R] [IsTopologicalRing R]

/-
`TopModuleCat R` is the canonical owner used in Definition 5.30.10. Mathlib supplies both
source clauses as global proposition instances: colimits are constructed on the underlying
modules, while `TopModuleCat.indiscreteAdj` makes the forgetful functor a left adjoint and hence
colimit-preserving. Separate tagged checks expose the independent clauses without a redundant
conjunction theorem. The owner is more general, but this source-facing check block retains the
source's `[IsTopologicalRing R]` setup.
-/

/- Lemma 5.30.12 (1): the category `TopModuleCat R` of topological `R`-modules has all small
colimits. -/
@[stacks 0B27 "topological modules have all small colimits"]
#check (inferInstance : HasColimits (TopModuleCat R))

/- Lemma 5.30.12 (2): the forgetful functor from `TopModuleCat R` to `ModuleCat R` preserves all
small colimits. -/
@[stacks 0B27 "colimits commute with the forgetful functor to modules"]
#check (inferInstance : PreservesColimits (forget₂ (TopModuleCat R) (ModuleCat R)))
