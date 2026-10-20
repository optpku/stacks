/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.ConstructibleTopology.Profinite
import StacksCheckRecall

@[expose] public section

/- Lemma 5.23.8: the standard separation, specialization, and patch-topology
criteria for a spectral space to be profinite are equivalent. -/
@[stacks 0905]
#check SpectralSpace.profinite_criteria
