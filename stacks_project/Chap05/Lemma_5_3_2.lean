/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Maps.Equalizer
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 5.3.2

Closed graphs are the one-map specialization of the reusable equality-locus API.
-/

/- Lemma 5.3.2: the graph of a continuous map into a Hausdorff space is closed. -/
@[stacks 08ZF]
#check Continuous.isClosed_graph
