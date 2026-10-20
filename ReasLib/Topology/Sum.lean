module

public import Mathlib.Topology.Sober
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Topological Sums

Reflection of separation and sobriety obstructions along the two canonical
summand embeddings.
-/

@[expose] public section

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

namespace Sum

/-- Example 5.8.11: a topological sum cannot be Kolmogorov when its left summand is not
Kolmogorov. -/
@[stacks 0B34 "Kolmogorov failure reflects to the left summand"]
theorem not_t0_of_not_t0_left (hX : ¬ T0Space X) : ¬ T0Space (X ⊕ Y) := sorry

/-- Example 5.8.11: a topological sum cannot be quasi-sober when its right summand is not
quasi-sober. -/
@[stacks 0B34 "quasi-sobriety failure reflects to the right summand"]
theorem not_quasiSober_of_not_quasiSober_right (hY : ¬ QuasiSober Y) :
    ¬ QuasiSober (X ⊕ Y) := sorry

end Sum
