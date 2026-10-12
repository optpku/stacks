/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.MulAction

@[expose] public section

namespace OpenSubgroup

universe u v

/-- The open subgroup stabilizing a point of a continuous action on a discrete space. -/
noncomputable def stabilizer (G : Type u) {A : Type v} [Group G] [TopologicalSpace G]
    [TopologicalSpace A] [MulAction G A] [ContinuousSMul G A] [DiscreteTopology A]
    (a : A) : OpenSubgroup G where
  toSubgroup := MulAction.stabilizer G a
  isOpen' := stabilizer_isOpen G a

/-- The underlying subgroup of the open stabilizer is the point stabilizer. -/
theorem stabilizer_toSubgroup (G : Type u) {A : Type v} [Group G] [TopologicalSpace G]
    [TopologicalSpace A] [MulAction G A] [ContinuousSMul G A] [DiscreteTopology A]
    (a : A) : (stabilizer G a).toSubgroup = MulAction.stabilizer G a := sorry

/-- Membership in the open stabilizer is equivalent to fixing the stabilized point. -/
theorem mem_stabilizer (G : Type u) {A : Type v} [Group G] [TopologicalSpace G]
    [TopologicalSpace A] [MulAction G A] [ContinuousSMul G A] [DiscreteTopology A]
    (a : A) {g : G} : g ∈ stabilizer G a ↔ g • a = a := sorry

end OpenSubgroup
