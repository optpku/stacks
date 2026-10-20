/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Noetherian.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 5.9.6

The local-connectedness instance belongs to the reusable locally Noetherian API.
-/

/- Lemma 5.9.6: a locally Noetherian topological space is locally connected. -/
@[stacks 04MF]
#check @TopologicalSpace.LocallyNoetherianSpace.locallyConnectedSpace
