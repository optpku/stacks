/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Jacobson.ClosedPoints
import StacksCheckRecall

@[expose] public section

/- Lemma 5.18.4 (1): Jacobsonness is local on an open cover. -/
@[stacks 005W "Jacobson spaces are local on open covers"]
#check TopologicalSpace.IsOpenCover.jacobsonSpace_iff

/- Lemma 5.18.4 (2): closed points are the union of the closed points of the
members of an open cover. -/
@[stacks 005W "closed points are the union of those in the cover members"]
#check TopologicalSpace.IsOpenCover.closedPoints_eq_iUnion_image
