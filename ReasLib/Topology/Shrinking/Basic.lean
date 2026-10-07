module

public import Mathlib.Topology.Sets.OpenCover
public import Mathlib.Topology.ShrinkingLemma
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Same-index shrinkings of open covers

Mathlib's shrinking lemma handles point-finite covers. This leaf records the
compact normal same-index consequence used by finite-refinement arguments.
-/

@[expose] public section

open Set TopologicalSpace

universe u v

namespace TopologicalSpace.IsOpenCover

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [NormalSpace X]
variable {ι : Type v}

/-- Lemma 5.13.4 (`09UV`), generalized to compact normal spaces: every open
cover admits a same-index shrinking with each closure contained in its original
member. -/
@[stacks 09UV "same-index shrinking of a compact normal open cover"]
theorem exists_shrinking {U : ι → Opens X} (hU : IsOpenCover U) :
    ∃ V : ι → Opens X, IsOpenCover V ∧ ∀ i, closure (V i) ⊆ (U i : Set X) := sorry

end TopologicalSpace.IsOpenCover
