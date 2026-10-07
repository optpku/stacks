module

public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.LocallyFinite
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Lemma_66_4_6_Topology

/-!
# Local finiteness of irreducible components

On a locally Noetherian algebraic space, the irreducible components of any
closed subset of the points space form a locally finite family.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 72.6.1: Let `S` be a scheme and let `X` be a locally Noetherian
algebraic space over `S`. If `T` is a closed subset of `Points X`, then the
collection of irreducible components of `T` is locally finite. -/
@[stacks 0EE5]
theorem locallyFinite_irreducibleComponents {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsLocallyNoetherian X] {T : Set (Points X)}
    (hT : IsClosed T) :
    LocallyFinite fun W : irreducibleComponents T ↦ Subtype.val '' (W : Set T) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
