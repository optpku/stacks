module

public import Mathlib.Topology.Sober
public import Mathlib.Topology.Order
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Indiscrete Spaces

Separation and sobriety consequences of the indiscrete topology that are not
currently exposed by Mathlib.
-/

@[expose] public section

universe u

variable {X : Type u} [TopologicalSpace X]

namespace IndiscreteTopology

/-- Every indiscrete topological space is an `R1Space`. -/
@[stacks 0B32 "indiscrete spaces are quasi-sober through the R1 property"]
instance r1Space [IndiscreteTopology X] : R1Space X := sorry

/-- A nontrivial indiscrete topological space is not Kolmogorov. -/
@[stacks 0B32 "nontrivial indiscrete spaces are not Kolmogorov"]
theorem not_t0 [IndiscreteTopology X] [Nontrivial X] : ¬ T0Space X := sorry

/-- The two-point space with the indiscrete topology is not Kolmogorov. -/
theorem notT0WithTopologyBool : ¬ T0Space (WithTopology Bool ⊤) := sorry

end IndiscreteTopology
