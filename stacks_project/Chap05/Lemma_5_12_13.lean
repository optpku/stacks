/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Noetherian.Compactness
import StacksCheckRecall

@[expose] public section

/- Lemma 5.12.13 (1): every Noetherian topological space is quasi-compact. -/
@[stacks 04ZA "quasi-compactness of Noetherian spaces"]
#check @TopologicalSpace.NoetherianSpace.compactSpace

/- Lemma 5.12.13 (2): every subset of a Noetherian topological space is retrocompact. -/
@[stacks 04ZA "retrocompactness of subsets of Noetherian spaces"]
#check @TopologicalSpace.NoetherianSpace.isRetrocompact
