/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Compactness.ClosedPoints
import StacksCheckRecall

@[expose] public section

/- Lemma 5.12.8: every nonempty quasi-compact Kolmogorov space has a closed point. -/
@[stacks 005E]
#check @CompactSpace.exists_closedPoint
