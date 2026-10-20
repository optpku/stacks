module

public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Irreducible

@[expose] public section

namespace TopologicalSpace.NoetherianSpace

/-- A Noetherian topological space has finitely many irreducible components. -/
theorem finite_irreducibleComponents_of_noetherian {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] : (irreducibleComponents X).Finite :=
  finite_irreducibleComponents

end TopologicalSpace.NoetherianSpace

namespace TopologicalSpace

/-- Every topological space is the union of its irreducible components. -/
theorem sUnion_irreducibleComponents {X : Type*} [TopologicalSpace X] :
    ⋃₀ irreducibleComponents X = Set.univ :=
  _root_.sUnion_irreducibleComponents

end TopologicalSpace
