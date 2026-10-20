/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Compactness.Compact
import StacksCheckRecall

@[expose] public section

/- Lemma 5.12.3: via Definition 5.12.1, quasi-compactness of spaces is the canonical owner
`CompactSpace`, and the closed-subset consequence is exactly the canonical theorem
`IsClosed.isCompact`. -/
@[stacks 005C "closed subsets of quasi-compact spaces"]
#check IsClosed.isCompact
