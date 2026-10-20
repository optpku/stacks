/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Category.TopCat.Limits.Cofiltered
import StacksCheckRecall

@[expose] public section

/- Lemma 5.14.2 (1): every open subset of a cofiltered `TopCat` limit is a
union of pullbacks of stagewise open subsets. -/
@[stacks 0A2P "opens are unions of stagewise pullbacks"]
#check TopCat.IsLimit.open_eq_iUnion_preimage

/- Lemma 5.14.2 (2): every quasi-compact open subset of a cofiltered `TopCat`
limit is pulled back from one stage. -/
@[stacks 0A2P "quasi-compact opens descend to one stage"]
#check TopCat.IsLimit.compactOpen_eq_preimage
