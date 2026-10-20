/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Maps.Proper.Projection
import StacksCheckRecall

@[expose] public section

/- Lemma 5.17.3: a topological space is compact if and only if every product
projection onto an ambient base is a closed map. -/
@[stacks 005P]
#check compactSpace_iff_forall_isClosedMap_fst
