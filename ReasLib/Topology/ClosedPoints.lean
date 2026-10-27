/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Closed points

Specialization criteria and transport results for Mathlib's canonical set `closedPoints X`.
-/

@[expose] public section

open Set Topology TopologicalSpace

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- A point admitting a distinct specialization is not closed. -/
theorem Specializes.not_mem_closedPoints {x y : X} (hxy : x ⤳ y) (hne : x ≠ y) :
    x ∉ closedPoints X := sorry

/-- If every point admits a distinct specialization, then the space has no closed points. -/
@[stacks 01IY "closed-point obstruction from specialization"]
theorem closedPoints_eq_empty_of_specializes_ne
    (h : ∀ x : X, ∃ y : X, x ≠ y ∧ x ⤳ y) :
    closedPoints X = ∅ := sorry

namespace Homeomorph

/-- A homeomorphism pulls back the closed points of its target to the closed points of its
source. -/
theorem preimage_closedPoints (e : X ≃ₜ Y) :
    e ⁻¹' closedPoints Y = closedPoints X := sorry

/-- A homeomorphism maps the closed points of its source onto the closed points of its target. -/
theorem image_closedPoints (e : X ≃ₜ Y) :
    e '' closedPoints X = closedPoints Y := sorry

/-- Having a closed point is invariant under homeomorphism. -/
theorem closedPoints_nonempty_iff (e : X ≃ₜ Y) :
    (closedPoints X).Nonempty ↔ (closedPoints Y).Nonempty := sorry

/-- A space without closed points cannot be homeomorphic to a space with a closed point. -/
@[stacks 02HZ "closed-point obstruction to a homeomorphism"]
theorem not_exists_of_closedPoints_eq_empty
    (hX : closedPoints X = ∅) (hY : (closedPoints Y).Nonempty) :
    ¬ Nonempty (X ≃ₜ Y) := sorry

end Homeomorph
namespace TopologicalSpace

/-- The range of a finite family of closed points is closed. -/
theorem isClosed_range_closedPoints {ι : Type*} [Finite ι] (x : ι → X)
    (hx : ∀ i, x i ∈ closedPoints X) : IsClosed (Set.range x) :=
  sorry

end TopologicalSpace
