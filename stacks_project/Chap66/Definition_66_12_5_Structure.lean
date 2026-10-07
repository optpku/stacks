module

public import Mathlib.Topology.Sets.Closeds
public import stacks_project.Chap66.Lemma_66_12_3

/-!
# Algebraic space structures on closed subsets

A closed subset of the points of an algebraic space may carry many algebraic space structures,
each realized by a closed subspace with that underlying point-set.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- An algebraic space structure on a closed subset `Z` of `Points X` is a closed subspace of `X`
whose underlying point-set is `Z`. -/
structure ClosedSubspaceStructure (Z : Closeds (Points X)) where
  /-- The closed subspace realizing the structure. -/
  subspace : ClosedSubspace X
  /-- The realizing closed subspace has the prescribed point-set. -/
  pointsSet_eq : subspace.pointsSet = Z.carrier

namespace ClosedSubspaceStructure

variable {Z : Closeds (Points X)}

/-- The algebraic space structure on `Z` determined by a closed subspace with that point-set. -/
def ofSubspace (W : ClosedSubspace X) (h : W.pointsSet = Z.carrier) :
    ClosedSubspaceStructure Z where
  subspace := W
  pointsSet_eq := h

/-- The algebraic space underlying a closed-subspace structure. -/
abbrev space (T : ClosedSubspaceStructure Z) : AlgebraicSpace S :=
  T.subspace.X

/-- The inclusion of a closed-subspace structure into the ambient algebraic space. -/
abbrev ι (T : ClosedSubspaceStructure Z) : T.space ⟶ X :=
  T.subspace.ι

/-- The underlying space of a closed-subspace structure is the space of its realizing closed
subspace. -/
theorem space_eq (T : ClosedSubspaceStructure Z) : T.space = T.subspace.X :=
  sorry

/-- The inclusion of a closed-subspace structure is the inclusion of its realizing closed
subspace. -/
theorem ι_eq (T : ClosedSubspaceStructure Z) : T.ι = T.subspace.ι :=
  sorry

/-- A closed-subspace structure is a closed immersion into `X` with the prescribed point-set. -/
theorem spec (T : ClosedSubspaceStructure Z) :
    IsClosedImmersion T.ι ∧ T.subspace.pointsSet = Z.carrier :=
  sorry

/-- The closed subspace recovered from `ofSubspace` is the given closed subspace. -/
theorem ofSubspace_subspace (W : ClosedSubspace X) (h : W.pointsSet = Z.carrier) :
    (ofSubspace W h).subspace = W :=
  sorry

end ClosedSubspaceStructure

end AlgebraicGeometry.AlgebraicSpace
