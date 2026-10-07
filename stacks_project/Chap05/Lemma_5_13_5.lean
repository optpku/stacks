module

public import ReasLib.Topology.Shrinking.Tuplewise
import StacksCheckRecall

@[expose] public section

open Set TopologicalSpace

universe u v w

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
variable {ι : Type v}

namespace TopologicalSpace.IsOpenCover

#check TopologicalSpace.IsTuplewiseShrinkingRefinement
#check TopologicalSpace.isTuplewiseShrinkingRefinement_iff
#check exists_finite_tuplewise_shrinking_refinement

/- Lemma 5.13.5: a compact Hausdorff open cover admits a shrinking refinement
whose realized `(p + 1)`-fold intersections are subordinate to prescribed covers
of the corresponding intersections of the original cover. -/
@[stacks 09UW]
#check fun {U : ι → Opens X} (hU : IsOpenCover U) (p : ℕ)
    {κ : (Fin (p + 1) → ι) → Type w}
    (W : ∀ s : Fin (p + 1) → ι, κ s → Opens X)
    (hW_cover : ∀ s : Fin (p + 1) → ι,
      (⋂ a : Fin (p + 1), (U (s a) : Set X)) = ⋃ k, (W s k : Set X)) ↦
  exists_tuplewise_shrinking_refinement hU p W hW_cover

end TopologicalSpace.IsOpenCover
