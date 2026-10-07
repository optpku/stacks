module

public import ReasLib.Topology.NowhereDense.OpenCover
import StacksCheckRecall

@[expose] public section

open Set TopologicalSpace

universe u v

variable {X : Type u} [TopologicalSpace X]
variable {ι : Type v} {U : ι → Opens X} {T : Set X}

/- Lemma 5.21.4: nowhere denseness is local on an open cover. -/
@[stacks 03HP]
#check fun (hU : IsOpenCover U)
    (hT : ∀ i, IsNowhereDense (Subtype.val ⁻¹' T : Set (U i))) ↦
  (hU.isNowhereDense_iff_preimage (T := T)).2 hT
