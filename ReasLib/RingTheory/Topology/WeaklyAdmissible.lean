/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Algebra.TopologicallyNilpotent
public import ReasLib.RingTheory.Topology.Adic.Complete

/-!
# Weak ideals of definition and weakly admissible rings

A weak ideal of definition is an open ideal of topologically nilpotent elements.
A linearly topologized ring is weakly pre-admissible when it has such an ideal, and
weakly admissible when it is weakly pre-admissible and complete, including
separated.
-/

@[expose] public section

universe u

namespace TopologicalRing

section

variable {R : Type u} [CommRing R] [TopologicalSpace R]

/-- An element of a commutative topological ring is topologically nilpotent when
its powers converge to zero. -/
def IsTopologicallyNilpotent (f : R) : Prop :=
  _root_.IsTopologicallyNilpotent f

namespace Ideal

/-- An ideal is a weak ideal of definition when it is open and every element is
topologically nilpotent. -/
def IsWeakIdealOfDefinition (I : Ideal R) : Prop :=
  IsOpen (I : Set R) ∧ ∀ f ∈ I, IsTopologicallyNilpotent f

/-- A weak ideal of definition is exactly an open ideal of topologically nilpotent
elements. -/
theorem isWeakIdealOfDefinition_iff (I : Ideal R) :
    IsWeakIdealOfDefinition I ↔
      IsOpen (I : Set R) ∧ ∀ f ∈ I, IsTopologicallyNilpotent f := sorry

/-- Under a linear topology, a weak ideal of definition is an open ideal contained
in the topological nilradical. -/
theorem isWeakIdealOfDefinition_iff_le_topologicalNilradical [IsLinearTopology R R]
    (I : Ideal R) :
    IsWeakIdealOfDefinition I ↔
      IsOpen (I : Set R) ∧ I ≤ topologicalNilradical R := sorry

/-- An ideal of definition is a weak ideal of definition. -/
theorem IsIdealOfDefinition.isWeakIdealOfDefinition {I : Ideal R}
    (hI : IsIdealOfDefinition I) : IsWeakIdealOfDefinition I := sorry

namespace IsWeakIdealOfDefinition

/-- A weak ideal of definition is open. -/
theorem isOpen {I : Ideal R} (hI : IsWeakIdealOfDefinition I) : IsOpen (I : Set R) :=
  sorry

/-- Every element of a weak ideal of definition is topologically nilpotent. -/
theorem isTopologicallyNilpotent {I : Ideal R} (hI : IsWeakIdealOfDefinition I) {f : R}
    (hf : f ∈ I) : _root_.IsTopologicallyNilpotent f := sorry

/-- The intersection of a weak ideal of definition with an open ideal is again a
weak ideal of definition. -/
theorem inf_of_isOpen {I J : Ideal R} (hI : IsWeakIdealOfDefinition I)
    (hJ : IsOpen (J : Set R)) : IsWeakIdealOfDefinition (I ⊓ J) := sorry

end IsWeakIdealOfDefinition

end Ideal

/-- A weakly pre-admissible ring is a linearly topologized topological ring that
has a weak ideal of definition. -/
class IsWeaklyPreadmissibleRing (R : Type u) [CommRing R] [TopologicalSpace R] : Prop
    extends IsTopologicalRing R, IsLinearTopology R R where
  /-- A weakly pre-admissible ring has a weak ideal of definition. -/
  exists_ideal_isWeakIdealOfDefinition : ∃ I : Ideal R, Ideal.IsWeakIdealOfDefinition I

/-- A linearly topologized topological ring is weakly pre-admissible exactly when it
has a weak ideal of definition. -/
theorem isWeaklyPreadmissibleRing_iff [IsTopologicalRing R] [IsLinearTopology R R] :
    IsWeaklyPreadmissibleRing R ↔ ∃ I : Ideal R, Ideal.IsWeakIdealOfDefinition I := sorry

/-- A pre-admissible ring is weakly pre-admissible. -/
instance instIsWeaklyPreadmissibleRing [IsPreadmissibleRing R] :
    IsWeaklyPreadmissibleRing R := sorry

/-- A weakly admissible ring is a complete separated weakly pre-admissible ring. -/
class IsWeaklyAdmissibleRing (R : Type u) [CommRing R] [TopologicalSpace R] : Prop
    extends IsWeaklyPreadmissibleRing R where
  /-- The ambient topology is separated. -/
  isT2 : T2Space R
  /-- The ambient additive uniformity is complete. -/
  isComplete : @CompleteSpace R (IsTopologicalAddGroup.rightUniformSpace R)

/-- A weakly pre-admissible ring is weakly admissible exactly when it is separated
and complete for the additive uniformity. -/
theorem isWeaklyAdmissibleRing_iff [IsWeaklyPreadmissibleRing R] :
    IsWeaklyAdmissibleRing R ↔
      T2Space R ∧ @CompleteSpace R (IsTopologicalAddGroup.rightUniformSpace R) := sorry

/-- A weakly admissible ring is separated. -/
instance instT2SpaceOfIsWeaklyAdmissibleRing [h : IsWeaklyAdmissibleRing R] : T2Space R :=
  h.isT2

/-- A weakly admissible ring is complete for its additive uniformity. -/
instance instCompleteSpaceOfIsWeaklyAdmissibleRing [h : IsWeaklyAdmissibleRing R] :
    @CompleteSpace R (IsTopologicalAddGroup.rightUniformSpace R) := h.isComplete

/-- An admissible ring is weakly admissible. -/
instance instIsWeaklyAdmissibleRing [IsAdmissibleRing R] : IsWeaklyAdmissibleRing R :=
  sorry

end

end TopologicalRing
