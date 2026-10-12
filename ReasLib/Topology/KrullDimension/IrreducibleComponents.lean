/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.NoetherianSpace

@[expose] public section

open TopologicalSpace

universe u

/-- On a Noetherian space, topological Krull dimension is the indexed supremum of the
dimensions of the irreducible components. -/
theorem topologicalKrullDim_eq_iSup_irreducibleComponents
    {X : Type u} [TopologicalSpace X] [NoetherianSpace X] :
    topologicalKrullDim X =
      ⨆ Z : irreducibleComponents X, topologicalKrullDim (Z : Set X) := sorry
