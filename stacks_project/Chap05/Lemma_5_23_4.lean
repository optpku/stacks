/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.ConstructibleTopology.Maps
import StacksCheckRecall

@[expose] public section

/- Lemma 5.23.4: a continuous map of spectral spaces is spectral exactly when
it is constructible-topology continuous. -/
@[stacks 0G1J]
#check Continuous.isSpectralMap_iff_constructibleTopology
