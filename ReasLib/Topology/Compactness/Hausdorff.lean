module

public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

namespace TopologicalSpace

/-- A topological space is compact Hausdorff when it is both quasi-compact and Hausdorff. -/
def IsCompactHausdorff (X : Type u) [TopologicalSpace X] : Prop :=
  CompactSpace X ∧ T2Space X

end TopologicalSpace
