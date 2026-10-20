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
# Lemma 5.9.3

The reusable image theorems are owned by `ReasLib.Topology.Noetherian`.
-/

/- Lemma 5.9.3 (1): the image of a Noetherian topological space under a continuous map is
Noetherian for the induced topology. -/
@[stacks 04Z8 "continuous images of Noetherian spaces"]
#check @TopologicalSpace.NoetherianSpace.range

/- Lemma 5.9.3 (2): the image of a locally Noetherian space under a continuous open map is
locally Noetherian for the induced topology. -/
@[stacks 04Z8 "open continuous images of locally Noetherian spaces"]
#check @TopologicalSpace.LocallyNoetherianSpace.range
