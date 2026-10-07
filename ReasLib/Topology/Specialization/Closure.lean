module

public import Mathlib.Topology.Inseparable

@[expose] public section

universe u

/-- A point belongs to the closure of a singleton exactly when the singleton's
point specializes to it. -/
theorem mem_closure_singleton_iff_specializes {X : Type u} [TopologicalSpace X]
    (x x' : X) : x ∈ closure ({x'} : Set X) ↔ x' ⤳ x := sorry
