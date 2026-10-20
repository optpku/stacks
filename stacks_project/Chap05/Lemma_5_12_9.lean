/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Compactness.ClosedPoints
import StacksCheckRecall

@[expose] public section

/- Lemma 5.12.9: in a quasi-compact Kolmogorov space, the subset of closed points is compact. -/
@[stacks 08ZM]
#check @CompactSpace.isCompact_closedPoints
