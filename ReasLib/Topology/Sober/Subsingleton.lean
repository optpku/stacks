module

public import ReasLib.Topology.Sober.Hausdorff
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Subsingleton Sober Spaces

The canonical sober-space consequence of a subsingleton carrier.
-/

@[expose] public section

universe u

variable {X : Type u} [TopologicalSpace X]

/-- Example 5.8.10: every subsingleton topological space is sober, expressed by `T0Space` and
`QuasiSober`. -/
@[stacks 0B33 "singleton subspaces are sober"]
theorem Subsingleton.sober [Subsingleton X] : T0Space X ∧ QuasiSober X := by
  exact T2Space.sober
