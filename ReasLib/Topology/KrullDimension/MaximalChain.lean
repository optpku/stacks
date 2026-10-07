module

public import Mathlib.Topology.KrullDimension

@[expose] public section

universe u

open TopologicalSpace Order

/-- A topological space of finite Krull dimension `d` has a strictly decreasing chain
of irreducible closed subsets of length `d`. -/
theorem exists_gtRelSeries_length_eq_topologicalKrullDim
    {X : Type u} [TopologicalSpace X] {d : ℕ} (hdim : topologicalKrullDim X = d) :
    ∃ Z : RelSeries {(a, b) : IrreducibleCloseds X × IrreducibleCloseds X | a > b},
      Z.length = d :=
  sorry
