module

public import ReasLib.RingTheory.Topology.WeaklyAdmissible

/-!
# Weak admissibility of discrete rings
-/

@[expose] public section

universe u

namespace TopologicalRing

/-- A commutative ring with the discrete topology is weakly admissible. -/
instance instIsWeaklyAdmissibleRing_of_discreteTopology
    {R : Type u} [CommRing R] [TopologicalSpace R] [DiscreteTopology R] :
    IsWeaklyAdmissibleRing R :=
  sorry

end TopologicalRing
