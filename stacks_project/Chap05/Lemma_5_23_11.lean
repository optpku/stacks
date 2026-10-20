/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Spectral.Maps
import StacksCheckRecall

@[expose] public section

/- Lemma 5.23.11: a bijective spectral map that lifts specializations or
generalizations is a homeomorphism. -/
@[stacks 09XU]
#check IsSpectralMap.isHomeomorph_of_bijective_of_specializing_or_generalizing
