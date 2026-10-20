/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Spectral.Separation
import StacksCheckRecall

@[expose] public section

/- Lemma 5.23.7: two points in a spectral space have a common specialization or
disjoint open neighborhoods. -/
@[stacks 0904]
#check SpectralSpace.exists_commonSpecialization_or_separatedNhds
