/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sets.OpenCover

/-!
# Bases subordinate to an open cover

This module owns the purely topological basis of opens contained in a member of an indexed open
family. It deliberately has no sheaf or category-valued hypotheses.
-/

@[expose] public section

open TopologicalSpace
open TopologicalSpace.Opens

noncomputable section

universe u v

namespace TopologicalSpace.OpenCover

variable {X : Type u} [TopologicalSpace X]
variable {ι : Type v} {U : ι → Opens X}

/-- The opens of `X` contained in at least one member of an indexed open family. -/
def subordinateOpens (U : ι → Opens X) : Set (Opens X) :=
  { W | ∃ i, W ≤ U i }

/-- Membership in the subordinate opens is exactly containment in one member of the indexed
family. -/
@[simp] theorem mem_subordinateOpens_iff {W : Opens X} :
    W ∈ subordinateOpens U ↔ ∃ i, W ≤ U i := sorry

/-- If an indexed family covers `X`, its subordinate opens form a topological basis. -/
theorem subordinateOpens_isBasis (hU : IsOpenCover U) :
    Opens.IsBasis (subordinateOpens U) := sorry

end TopologicalSpace.OpenCover
