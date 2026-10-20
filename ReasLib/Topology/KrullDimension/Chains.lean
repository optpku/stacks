module

public import Mathlib.Topology.KrullDimension

@[expose] public section

universe u

/-- The topological Krull dimension is the supremum of the lengths of strictly increasing
chains of irreducible closed subsets, with value `⊥` when there are no such chains. -/
theorem topologicalKrullDim_eq_iSup_chainLength (X : Type u) [TopologicalSpace X] :
    topologicalKrullDim X =
      ⨆ chain : LTSeries (TopologicalSpace.IrreducibleCloseds X),
        (chain.length : WithBot ℕ∞) := sorry
