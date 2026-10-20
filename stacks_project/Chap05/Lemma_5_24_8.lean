/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Spectral.SpecializingPoints
import StacksCheckRecall

@[expose] public section

/-
Lemma 5.24.8 is owned by the spectral specializing-points API. The chapter path remains a tagged
reference surface for its spectrality and inverse-limit statements.
-/

/- Lemma 5.24.8 (1): the specializing-points difference is spectral. -/
@[stacks 0AP0 "spectrality of the difference"]
#check spectralSpace_specializingPoints_sdiff_constructible

/- Lemma 5.24.8 (2): inverse-limit presentation of the specializing-points difference. -/
@[stacks 0AP0 "inverse-limit presentation of the difference"]
#check specializingPointsSdiff_limitProperty
