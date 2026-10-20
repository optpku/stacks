/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Separation.Regular
import StacksCheckRecall

@[expose] public section

universe u

section

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]

/- Lemma 5.12.11: in a quasi-compact Hausdorff space, the connected component of a point is the
intersection of all open and closed subsets containing that point. This is exactly the canonical
mathlib theorem `connectedComponent_eq_iInter_isClopen`. -/
@[stacks 08ZN "connected components as intersections of clopen neighborhoods"]
#check connectedComponent_eq_iInter_isClopen

end
