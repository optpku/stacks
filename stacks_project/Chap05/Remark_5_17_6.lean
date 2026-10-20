/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Maps.Proper.Characterization
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Remark 5.17.6 records literature references for the implications among the four conditions in
Theorem 5.17.5 and concludes that all four are equivalent. The preceding theorem is therefore the
exact mathematical owner; this file adds the remark's source metadata without introducing a
second predicate or a weaker three-clause projection. -/
@[stacks 005S "literature references for the equivalent characterizations of proper maps"]
#check @Continuous.isProperMap_tfae
