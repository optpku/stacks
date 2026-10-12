/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Cofinite.Basic
public import Mathlib.Topology.Sober
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Pointed Cofinite Topology

A cofinite topology in which every nonempty open set is required to contain a
distinguished point.
-/

@[expose] public section

universe u

open Set

/-- Example 5.8.12: the topology whose basic open sets have finite complement and contain the
distinguished point. -/
@[implicit_reducible, stacks 0B35 "the pointed cofinite topology"]
protected def TopologicalSpace.pointedCofinite {X : Type u} (z : X) : TopologicalSpace X :=
  TopologicalSpace.generateFrom {s | sᶜ.Finite ∧ z ∈ s}

/-- The carrier equipped with the pointed cofinite topology determined by `z`. -/
abbrev PointedCofiniteTopology (X : Type u) (z : X) :=
  WithTopology X (TopologicalSpace.pointedCofinite z)

namespace PointedCofiniteTopology

variable {X : Type u}

/-- The identity equivalence from the underlying type to its pointed cofinite topology. -/
def of (z : X) : X ≃ PointedCofiniteTopology X z :=
  (WithTopology.equiv X (TopologicalSpace.pointedCofinite z)).symm

/-- The distinguished point in its pointed cofinite topology. -/
def point (z : X) : PointedCofiniteTopology X z := of z z

/-- The complement of the distinguished point in a pointed cofinite topology. -/
abbrev punctured (z : X) := {x : PointedCofiniteTopology X z // x ≠ point z}

/-- Example 5.8.12: the closed subsets are the whole space and the finite subsets avoiding the
distinguished point. -/
@[stacks 0B35 "closed sets in the pointed cofinite topology"]
theorem isClosed_iff (z : X) {s : Set (PointedCofiniteTopology X z)} :
    IsClosed s ↔ s = univ ∨ s.Finite ∧ point z ∉ s := sorry

/-- Example 5.8.12: every pointed cofinite topology is sober, expressed by `T0Space` and
`QuasiSober`. -/
@[stacks 0B35 "the pointed cofinite topology is sober"]
theorem sober (z : X) :
    T0Space (PointedCofiniteTopology X z) ∧ QuasiSober (PointedCofiniteTopology X z) := sorry

/-- Example 5.8.12: removing the distinguished point from an infinite pointed cofinite topology
does not leave a quasi-sober subspace. -/
@[stacks 0B35 "the punctured pointed cofinite topology is not quasi-sober"]
theorem punctured_not_quasiSober (z : X) [Infinite X] : ¬ QuasiSober (punctured z) := sorry

end PointedCofiniteTopology
