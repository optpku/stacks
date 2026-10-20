/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Shrinking.PrescribedIntersections
import StacksCheckRecall

@[expose] public section

/-
Lemma 5.13.6 is owned by the compact-subset shrinking API. The chapter entry retains only the
canonical predicate, its extensional interface, and the tagged existence theorem.
-/

#check TopologicalSpace.IsOpenShrinkingWithPrescribedIntersections
#check TopologicalSpace.isOpenShrinkingWithPrescribedIntersections_iff

/- Lemma 5.13.6: a compact subset of a locally compact Hausdorff space admits a shrinking with
prescribed `(p + 1)`-fold intersections. -/
@[stacks 09UX]
#check IsCompact.exists_open_shrinking_with_prescribed_intersections
