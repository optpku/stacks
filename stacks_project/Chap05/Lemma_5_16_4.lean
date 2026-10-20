/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Constructible.Neighborhood
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 5.16.4

The constructible neighborhood criterion is owned by
`ReasLib.Topology.Constructible.Neighborhood`.
-/

/- Lemma 5.16.4: dense irreducible traces characterize constructible neighborhoods. -/
@[stacks 0540]
#check @Topology.IsConstructible.mem_nhds_iff_forall_dense_irreducibleCloseds_trace
