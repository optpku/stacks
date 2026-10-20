/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Spectral.Limit.Spectral
import StacksCheckRecall

@[expose] public section

/-
Lemma 5.24.5 recalls spectrality of a cofiltered spectral inverse limit and of its projections.
-/

/- Lemma 5.24.5 (1): a limiting cone over a cofiltered spectral diagram has a spectral point. -/
@[stacks 0A2Z "spectral inverse limit"]
#check spectralSpace_of_isLimit_of_cofiltered_spectral_diagram

/- Lemma 5.24.5 (2): projections from that limiting cone are spectral maps. -/
@[stacks 0A2Z "spectral limit projections"]
#check isSpectralMap_projection_of_isLimit_of_cofiltered_spectral_diagram
