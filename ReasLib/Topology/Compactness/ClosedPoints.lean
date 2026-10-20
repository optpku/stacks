/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.ClosedPoints
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Closed Points of Compact Spaces

Compact Kolmogorov spaces have enough closed points for the compactness API
of the canonical set `closedPoints X`.
-/

@[expose] public section

universe u

variable {X : Type u} [TopologicalSpace X]

namespace TopologicalSpace

/-- A nonempty closed subset of a compact Kolmogorov space contains a closed point of the ambient
space. -/
@[stacks 005E "closed points in nonempty closed subsets"]
theorem _root_.IsClosed.exists_mem_closedPoints
    [CompactSpace X] [T0Space X] {Z : Set X} (hZ : IsClosed Z) (hZne : Z.Nonempty) :
    ∃ x ∈ Z, x ∈ closedPoints X := sorry

end TopologicalSpace

namespace CompactSpace

/-- Lemma 5.12.8: every nonempty compact Kolmogorov space has a closed point. -/
@[stacks 005E "closed points in nonempty quasi-compact Kolmogorov spaces"]
theorem exists_closedPoint [CompactSpace X] [T0Space X] [Nonempty X] :
    (closedPoints X).Nonempty := sorry

/-- Lemma 5.12.9: the closed-point subset of a compact Kolmogorov space is compact. -/
@[stacks 08ZM "compactness of the closed-point subset"]
theorem isCompact_closedPoints [CompactSpace X] [T0Space X] :
    IsCompact (closedPoints X) := sorry

end CompactSpace
