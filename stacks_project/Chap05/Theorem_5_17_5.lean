/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Maps.Proper.Characterization
import StacksCheckRecall

@[expose] public section

/- Theorem 5.17.5: the four standard continuous proper-map formulations are
equivalent. -/
@[stacks 005R]
#check @Continuous.isProperMap_tfae
