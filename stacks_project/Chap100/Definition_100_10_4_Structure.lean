/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sets.Closeds
public import stacks_project.Chap100.Lemma_100_10_1_Points

/-!
# Algebraic stack structures on closed subsets

A closed subset of the points of an algebraic stack may carry many algebraic stack
structures, each realized by a closed substack with that underlying point-set.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

/-- An algebraic stack structure on a closed subset `Z` of `Points X` is a closed
substack of `X` whose underlying point-set is `Z`. -/
structure ClosedSubstackStructure (Z : Closeds (Points X)) where
  /-- The closed substack realizing the structure. -/
  substack : ClosedSubstack X
  /-- The realizing closed substack has the prescribed point-set. -/
  pointsSet_eq : substack.pointsSet = Z.carrier

namespace ClosedSubstackStructure

variable {Z : Closeds (Points X)}

/-- The algebraic stack structure on `Z` determined by a closed substack with that
point-set. -/
def ofSubstack (W : ClosedSubstack X) (h : W.pointsSet = Z.carrier) :
    ClosedSubstackStructure Z where
  substack := W
  pointsSet_eq := h

/-- The algebraic stack underlying a closed-substack structure. -/
abbrev Y (T : ClosedSubstackStructure Z) : GroupoidsOver S :=
  T.substack.Y

/-- The inclusion of a closed-substack structure into the ambient algebraic stack. -/
abbrev ι (T : ClosedSubstackStructure Z) : T.Y ⟶ X :=
  T.substack.ι

/-- The underlying stack of a closed-substack structure is the stack of its realizing
closed substack. -/
theorem Y_eq (T : ClosedSubstackStructure Z) : T.Y = T.substack.Y :=
  sorry

/-- The inclusion of a closed-substack structure is the inclusion of its realizing
closed substack. -/
theorem ι_eq (T : ClosedSubstackStructure Z) : T.ι = T.substack.ι :=
  sorry

/-- A closed-substack structure is a closed immersion into `X` with the prescribed
point-set. -/
theorem spec (T : ClosedSubstackStructure Z) :
    ClosedImmersion T.ι ∧ T.substack.pointsSet = Z.carrier :=
  sorry

/-- The closed substack recovered from `ofSubstack` is the given closed substack. -/
theorem ofSubstack_substack (W : ClosedSubstack X) (h : W.pointsSet = Z.carrier) :
    (ofSubstack W h).substack = W :=
  sorry

end ClosedSubstackStructure

end AlgebraicGeometry.AlgebraicStack
