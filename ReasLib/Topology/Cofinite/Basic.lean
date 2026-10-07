module

public import Mathlib.Topology.Sober
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Cofinite Topology

Sobriety properties of Mathlib's canonical `CofiniteTopology` construction.
-/

@[expose] public section

universe u

variable {X : Type u}

namespace CofiniteTopology

/-- Example 5.8.10: the cofinite topology on an infinite type is not quasi-sober. -/
@[stacks 0B33 "the infinite cofinite space is not quasi-sober"]
theorem not_quasiSober [Infinite X] : ¬ QuasiSober (CofiniteTopology X) := by
  intro h
  obtain ⟨x, hx⟩ := h.sober (IrreducibleSpace.isIrreducible_univ _) isClosed_univ
  rw [isGenericPoint_def, closure_singleton] at hx
  haveI : Infinite (CofiniteTopology X) := CofiniteTopology.of.infinite_iff.mp inferInstance
  exact Set.infinite_univ.not_finite (hx ▸ Set.finite_singleton x)

end CofiniteTopology
