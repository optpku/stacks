/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Order.Filter.CountablyGenerated
public import Mathlib.Topology.Algebra.LinearTopology

/-!
# Countably indexed topological rings

A countably indexed topological ring admits a countable basis of open ideals at zero.
-/

@[expose] public section

universe u

open Filter Topology

namespace TopologicalRing

variable {R : Type u} [CommRing R] [TopologicalSpace R]

/-- A topological ring is countably indexed when it has a countable fundamental system of
open ideals. -/
class IsCountablyIndexed (R : Type u) [CommRing R] [TopologicalSpace R] : Prop where
  /-- There is a countable family of open ideals forming a neighborhood basis at `0`. -/
  exists_countable_open_ideal_basis :
    ∃ I : ℕ → Ideal R,
      (∀ n, IsOpen (I n : Set R)) ∧
        (nhds (0 : R)).HasBasis (fun _ : ℕ => True) (fun n => (I n : Set R))

/-- A countable family of open ideals forming a neighborhood basis at `0` makes the ring
countably indexed. -/
theorem IsCountablyIndexed.of_hasBasis {I : ℕ → Ideal R} (hI : ∀ n, IsOpen (I n : Set R))
    (hbasis : (nhds (0 : R)).HasBasis (fun _ : ℕ => True) (fun n => (I n : Set R))) :
    IsCountablyIndexed R := sorry

/-- Under a linear topology, countable indexing is equivalent to countably generated
neighborhoods of `0`. -/
theorem isCountablyIndexed_iff_nhds_isCountablyGenerated
    [IsTopologicalRing R] [IsLinearTopology R R] :
    IsCountablyIndexed R ↔ (nhds (0 : R)).IsCountablyGenerated := sorry

/-- A linearly topologized ring with countably generated neighborhoods of `0` is countably
indexed. -/
instance instIsCountablyIndexed [IsTopologicalRing R] [IsLinearTopology R R]
    [(nhds (0 : R)).IsCountablyGenerated] : IsCountablyIndexed R := sorry

end TopologicalRing
