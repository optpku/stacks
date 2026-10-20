/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Jacobson.Basic
import StacksCheckRecall

@[expose] public section

/- Lemma 5.18.3: a non-Jacobson Kolmogorov prespectral space has a non-closed
point whose singleton is locally closed. -/
@[stacks 02I7]
#check PrespectralSpace.exists_nonclosedPoint_with_locallyClosedSingleton
