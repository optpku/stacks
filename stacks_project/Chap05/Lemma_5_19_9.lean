/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.KrullDimension.Maps
import StacksCheckRecall

@[expose] public section

/- Lemma 5.19.9: a continuous surjective map lifting either specializations or
generalizations does not increase topological Krull dimension. -/
@[stacks 02JF]
#check @Continuous.topologicalKrullDim_le_of_surjective_of_specializing_or_generalizingMap
