/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Category.TopCat.Limits.Compact
import StacksCheckRecall

@[expose] public section

/- Lemma 5.14.5: the limit of compact Hausdorff topological spaces is compact. -/
@[stacks 08ZV]
#check TopCat.compactSpace_limit_of_compactSpace_t2Space
