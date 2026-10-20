/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Noetherian.Basic
public import Mathlib.Data.PNat.Order
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.Order.UpperLowerSetTopology
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Lower-Set Topology on Positive Naturals

The canonical lower-set topology on positive natural numbers and its local
Noetherianity properties.
-/

@[expose] public section

open Set TopologicalSpace

namespace Topology.WithLowerSet

/-- Example 5.9.5: the opens of the lower-set topology on positive naturals are empty, an initial
segment, or the whole space. -/
@[stacks 02HZ "open sets of the positive-integer lower-set topology"]
theorem pnat_isOpen_iff (s : Set (Topology.WithLowerSet ℕ+)) :
    IsOpen s ↔ s = ∅ ∨ (∃ n : ℕ+, s = Iic (toLowerSet n)) ∨ s = univ := sorry

/-- Example 5.9.5: positive naturals with the lower-set topology form a locally Noetherian
space. -/
@[stacks 02HZ "local Noetherianity of the positive-integer lower-set topology"]
instance pnatLocallyNoetherianSpace :
    LocallyNoetherianSpace (Topology.WithLowerSet ℕ+) := sorry

/-- Example 5.9.5: positive naturals with the lower-set topology have no closed points. -/
@[stacks 02HZ "absence of closed points in the positive-integer lower-set topology"]
theorem pnat_closedPoints_eq_empty :
    closedPoints (Topology.WithLowerSet ℕ+) = ∅ := sorry

end Topology.WithLowerSet
