/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Stratification.Refinement
import StacksCheckRecall

@[expose] public section

/- Lemma 5.28.8: finite (locally closed) partitions of Noetherian spaces admit finite good locally closed
refinements. -/
@[stacks 09Y5]
#check LocallyClosedPartition.exists_finite_good_refinement
