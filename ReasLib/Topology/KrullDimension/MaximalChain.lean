/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

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
