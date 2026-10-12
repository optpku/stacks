/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.GroupTheory.Finiteness
public import Mathlib.Topology.Algebra.Group.Basic

@[expose] public section

universe u

namespace TopologicalGroup

/-- A topological group is topologically finitely generated when it has a dense finitely generated
subgroup. -/
def IsFinitelyGenerated (G : Type u) [Group G] [TopologicalSpace G] : Prop :=
  ∃ H : Subgroup G, H.FG ∧ Dense (H : Set G)

/-- A topological group is finitely generated precisely when the closure of a finite tuple is
dense. -/
theorem isFinitelyGenerated_iff
    (G : Type u) [Group G] [TopologicalSpace G] :
    IsFinitelyGenerated G ↔
      ∃ r : ℕ, ∃ g : Fin r → G,
        Dense (Subgroup.closure (Set.range g) : Set G) := sorry

end TopologicalGroup
