module

public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Irreducible
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Connected Unions of Irreducible Components

This module records the finite irreducible-component deletion consequence of
connectedness.
-/

@[expose] public section

universe u

open Set

variable {X : Type u} [TopologicalSpace X] [ConnectedSpace X]

/-- Lemma 5.8.17: if a connected space has more than one irreducible component and exactly `n`
components, then omitting one component leaves a connected union of the remaining components. -/
@[stacks 0GM3]
theorem exists_connected_union_irreducibleComponents_except {n : ℕ}
    (hcount : (irreducibleComponents X).encard = n) (hn : 1 < n) :
    ∃ Z : irreducibleComponents X,
      IsConnected (⋃₀ (irreducibleComponents X \ {(Z : Set X)})) := sorry
