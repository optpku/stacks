/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Shrinking.Basic
import StacksCheckRecall

@[expose] public section

open Set TopologicalSpace

universe u v

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
variable {ι : Type v}

namespace TopologicalSpace.IsOpenCover

/- Lemma 5.13.4: a compact Hausdorff space admits a shrinking of any open cover,
indexed by the same family, such that each closure lies in its original member. -/
@[stacks 09UV]
#check fun {U : ι → Opens X} (hU : IsOpenCover U) ↦ hU.exists_shrinking

end TopologicalSpace.IsOpenCover
