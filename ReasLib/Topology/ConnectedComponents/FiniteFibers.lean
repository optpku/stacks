module

public import Mathlib.Topology.Connected.CardComponents
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Connected Components under Finite Fibers

This module records finite-fiber consequences for open and closed maps over a
connected target.
-/

@[expose] public section

universe u v

open Set Topology

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable [ConnectedSpace Y] {f : X → Y}

namespace IsOpenMap

/-- Lemma 5.7.7 (1): an open and closed map to a connected target has at most the cardinality of
one finite fiber many connected components. -/
@[stacks 07VB "bound on the number of connected components"]
theorem natCard_connectedComponents_le_ncard_preimage_singleton
    (hopen : IsOpenMap f) (hclosed : IsClosedMap f) {y : Y}
    (hyfin : (f ⁻¹' {y}).Finite) :
    Nat.card (ConnectedComponents X) ≤ (f ⁻¹' {y}).ncard := sorry

/-- Lemma 5.7.7 (2): under a finite-fiber open and closed map to a connected target, every
connected component of the source is clopen. -/
@[stacks 07VB "connected components are clopen"]
theorem isClopen_connectedComponent_of_finiteFiber
    (hopen : IsOpenMap f) (hclosed : IsClosedMap f) {y : Y}
    (hyfin : (f ⁻¹' {y}).Finite) (x : X) :
    IsClopen (connectedComponent x) := sorry

/-- Lemma 5.7.7 (3): the image of each source connected component is a nonempty clopen subset
of the connected target. -/
@[stacks 07VB "component images are nonempty and clopen"]
theorem image_connectedComponent_nonempty_and_isClopen_of_finiteFiber
    (hopen : IsOpenMap f) (hclosed : IsClosedMap f) {y : Y}
    (hyfin : (f ⁻¹' {y}).Finite) (x : X) :
    (f '' connectedComponent x).Nonempty ∧ IsClopen (f '' connectedComponent x) := sorry

/-- Lemma 5.7.7 (4): each connected component of the source maps onto the connected target. -/
@[stacks 07VB "every component maps onto the connected target"]
theorem image_connectedComponent_eq_univ_of_finiteFiber
    (hopen : IsOpenMap f) (hclosed : IsClosedMap f) {y : Y}
    (hyfin : (f ⁻¹' {y}).Finite) (x : X) :
    f '' connectedComponent x = Set.univ := sorry

end IsOpenMap
