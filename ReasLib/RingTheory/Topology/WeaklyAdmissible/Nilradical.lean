/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Topology.WeaklyAdmissible
public import ReasLib.RingTheory.Topology.TopologicalNilradical

@[expose] public section

universe u

namespace topologicalNilradical

/-- The topological nilradical of a weakly admissible ring is open. -/
theorem isOpen_of_isWeaklyAdmissible {A : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] :
    IsOpen (topologicalNilradical A : Set A) :=
  sorry

/-- The topological nilradical of a weakly admissible ring is a weak ideal of definition. -/
theorem isWeakIdealOfDefinition_of_isWeaklyAdmissible {A : Type u} [CommRing A]
    [TopologicalSpace A] [TopologicalRing.IsWeaklyAdmissibleRing A] :
    TopologicalRing.Ideal.IsWeakIdealOfDefinition (topologicalNilradical A) :=
  sorry

end topologicalNilradical
